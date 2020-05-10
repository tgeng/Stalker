package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Term => DbTerm, Elimination => DbElimination, Whnf}
import DbTerm.TWhnf
import Whnf._

enum Term {
  case TRedux(fn: QualifiedName, elims: List[Elimination])
  case TFunction(argName: String, argTy: Term, bodyTy: Term)
  case TUniverse(level: Int)
  case TData(qn: QualifiedName, params: List[Term])
  case TRecord(qn: QualifiedName, params: List[Term])
  case TId(ty: Term, left: Term, right: Term)
  case TVar(name: String, elims: List[Elimination])
  case TCon(con: String, args: List[Term])
  case TRefl

  def tt(using ctx: NameContext) : Result[DbTerm] = this match {
    case TRedux(fn, elims) => elims.liftMap(_.tt).map(DbTerm.TRedux(fn, _))
    case TFunction(argName, argTy, bodyTy) => for {
      dbArgTy <- argTy.tt
      dbBodyTy <- ctx.withName(argName) {
        bodyTy.tt
      }
    } yield TWhnf(WFunction(dbArgTy, dbBodyTy)(argName))
    case TUniverse(l) => Right(TWhnf(WUniverse(l)))
    case TData(qn, params) => params.liftMap(_.tt).map(p => TWhnf(WData(qn, p)))
    case TRecord(qn, params) => params.liftMap(_.tt).map(p => TWhnf(WRecord(qn, p)))
    case TId(ty, left, right) => for {
      dbTy <- ty.tt
      dbLeft <- left.tt
      dbRight <- right.tt
    } yield TWhnf(WId(dbTy, dbLeft, dbRight))
    case TVar(name, elims) => for {
      wElims <- elims.liftMap(_.tt)
      idx <- ctx.get(name)
    } yield TWhnf(WVar(idx, wElims))
    case TCon(con, args) => args.liftMap(_.tt).map(ts => TWhnf(WCon(con, ts)))
    case TRefl => Right(TWhnf(WRefl))
  }
}

enum Elimination {
  case ETerm(t: Term)
  case EProj(p: String)

  def tt(using ctx: NameContext) : Result[DbElimination] = this match {
    case ETerm(t) => t.tt.map(DbElimination.ETerm(_))
    case EProj(p) => Right(DbElimination.EProj(p))
  }
}
