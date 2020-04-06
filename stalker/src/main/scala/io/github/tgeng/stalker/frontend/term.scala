package io.github.tgeng.stalker.frontend

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.{Term => DbTerm, Elimination => DbElimination, Whnf}
import DbTerm.TWhnf
import Whnf._

enum Term {
  case TRedux(fn: QualifiedName, elims: List[Elimination])
  case TFunction(argName: String, argTy: Term, bodyTy: Term)
  case TUniverse(level: Int)
  case TData(qn: QualifiedName, params: List[Term])
  case TRecord(qn: QualifiedName, params: List[Term])
  case TId(ty: Term, left: Term, right: Term)
  case TVar(idx: Int, elims: List[Elimination])
  case TCon(con: String, args: List[Term])
  case TRefl
}

import Term._

extension termOps on (self: Term) {
  def toDbTerm(using ctx: NameContext) : Result[DbTerm] = self match {
    case TRedux(fn, elims) => elims.liftMap(_.toDbElimination).map(DbTerm.TRedux(fn, _))
    case TFunction(argName, argTy, bodyTy) => for {
      dbArgTy <- argTy.toDbTerm
      dbBodyTy <- ctx.withName(argName) {
        bodyTy.toDbTerm
      }
    } yield TWhnf(WFunction(dbArgTy, dbBodyTy)(argName))
    case TUniverse(l) => Right(TWhnf(WUniverse(l)))
    case TData(qn, params) => params.liftMap(_.toDbTerm).map(p => TWhnf(WData(qn, p)))
    case TRecord(qn, params) => params.liftMap(_.toDbTerm).map(p => TWhnf(WRecord(qn, p)))
    case TId(ty, left, right) => for {
      dbTy <- ty.toDbTerm
      dbLeft <- left.toDbTerm
      dbRight <- right.toDbTerm
    } yield TWhnf(WId(dbTy, dbLeft, dbRight))
    case TVar(idx, elims) => elims.liftMap(_.toDbElimination).map(es => TWhnf(WVar(idx, es)))
    case TCon(con, args) => args.liftMap(_.toDbTerm).map(ts => TWhnf(WCon(con, ts)))
    case TRefl => Right(TWhnf(WRefl))
  }
}

enum Elimination {
  case ETerm(t: Term)
  case EProj(p: String)
}

import Elimination._

extension eliminationOps on (self: Elimination) {
  def toDbElimination(using ctx: NameContext) : Result[DbElimination] = self match {
    case ETerm(t) => t.toDbTerm.map(DbElimination.ETerm(_))
    case EProj(p) => Right(DbElimination.EProj(p))
  }
}