package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Term => TtTerm, Elimination => TtElimination, Whnf, stringBindingOps, Binding => TtBinding}
import TtTerm.TWhnf
import Whnf._

case class Binding(name: String, ty: Term) {
  def tt(using ctx: NameContext) : TtBinding[TtTerm] = TtBinding(ty.tt)(name)
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

  def tt(using ctx: NameContext) : TtTerm = this match {
    case TRedux(fn, elims) => TtTerm.TRedux(fn, elims.map(_.tt))
    case TFunction(arg, bodyTy) => TWhnf(WFunction(
      arg.name ∷ arg.ty.tt, 
      ctx.withName(arg.name) {
        bodyTy.tt
      }))
    case TUniverse(l) => TWhnf(WUniverse(l))
    case TData(qn, params) => TWhnf(WData(qn, params.map(_.tt)))
    case TRecord(qn, params) => TWhnf(WRecord(qn, params.map(_.tt)))
    case TId(ty, left, right) => TWhnf(WId(ty.tt, left.tt, right.tt))
    case TVar(name, elims) => TWhnf(WVar(ctx(name), elims.map(_.tt)))
    case TCon(con, args) => TWhnf(WCon(con, args.map(_.tt)))
    case TRefl => TWhnf(WRefl)
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

  def tt(using ctx: NameContext) : TtElimination = this match {
    case ETerm(t) => TtElimination.ETerm(t.tt)
    case EProj(p) => TtElimination.EProj(p)
  }
}

import Elimination._

extension eliminationFeOps on (self: TtElimination) {
  def fe(using ctx: IndexedSeq[String]): Elimination = self match {
    case TtElimination.ETerm(t) => ETerm(t.fe)
    case TtElimination.EProj(p) => EProj(p)
  }
}