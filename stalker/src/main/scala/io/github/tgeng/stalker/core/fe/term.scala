package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Term => TtTerm, Elimination => TtElimination, Whnf, stringBindingOps, Binding => TtBinding}
import TtTerm.TWhnf
import Whnf._

case class Binding(name: String, ty: Term) {
  def tt(using ctx: NameContext) : Result[TtBinding[TtTerm]] = for {
    dbTerm <- ty.tt
  } yield TtBinding(dbTerm)(name)
}

enum Term {
  case TRedux(fn: QualifiedName, elims: List[Elimination])
  case TFunction(arg: Binding, bodyTy: Term)
  case TUniverse(level: Int)
  case TData(qn: QualifiedName, params: List[Term])
  case TRecord(qn: QualifiedName, params: List[Term])
  case TId(ty: Term, left: Term, right: Term)
  case TVar(name: String, elims: List[Elimination])
  case TCon(con: String, args: List[Term])
  case TRefl

  def tt(using ctx: NameContext) : Result[TtTerm] = this match {
    case TRedux(fn, elims) => elims.liftMap(_.tt).map(TtTerm.TRedux(fn, _))
    case TFunction(arg, bodyTy) => for {
      dbArgTy <- arg.ty.tt
      dbBodyTy <- ctx.withName(arg.name) {
        bodyTy.tt
      }
    } yield TWhnf(WFunction(arg.name ∷ dbArgTy, dbBodyTy))
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

import Term._

extension termFeOps on (self: TtTerm) {
  def fe(using ctx: IndexedSeq[String]): Term = self match {
    case TtTerm.TWhnf(whnf) => whnf.fe
    case TtTerm.TRedux(fn, elims) => TRedux(fn, elims.map(_.fe))
  }
}

extension whnfFeOps on (self: Whnf) {
  def fe(using ctx: IndexedSeq[String]): Term = self match {
    case WFunction(_A, _B) => TFunction(Binding(_A.name, _A.ty.fe), _B.fe(using _A.name +: ctx))
    case WUniverse(l) => TUniverse(l)
    case WData(qn, params) => TData(qn, params.map(_.fe))
    case WRecord(qn, params) => TRecord(qn, params.map(_.fe))
    case WId(ty, left, right) => TId(ty.fe, left.fe, right.fe)
    case WVar(idx, elims) => TVar(ctx(idx), elims.map(_.fe))
    case WCon(con, args) => TCon(con, args.map(_.fe))
    case WRefl => TRefl
  }
}

enum Elimination {
  case ETerm(t: Term)
  case EProj(p: String)

  def tt(using ctx: NameContext) : Result[TtElimination] = this match {
    case ETerm(t) => t.tt.map(TtElimination.ETerm(_))
    case EProj(p) => Right(TtElimination.EProj(p))
  }
}

import Elimination._

extension eliminationFeOps on (self: TtElimination) {
  def fe(using ctx: IndexedSeq[String]): Elimination = self match {
    case TtElimination.ETerm(t) => ETerm(t.fe)
    case TtElimination.EProj(p) => EProj(p)
  }
}