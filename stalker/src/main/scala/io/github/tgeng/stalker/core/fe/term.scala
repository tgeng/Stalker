package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Term => TtTerm, Elimination => TtElimination, Whnf, stringBindingOps, Binding => TtBinding, Level}
import io.github.tgeng.stalker.core.tt.builtins
import TtTerm.TWhnf
import Whnf._
import Level._

case class Binding(name: String, ty: Term) {
  def tt(using ctx: NameContext) : TtBinding[TtTerm] = TtBinding(ty.tt)(name)
}

enum Term {
  case TRedux(fn: QualifiedName, elims: List[Elimination])
  case TFunction(arg: Binding, bodyTy: Term)
  case TVar(name: String, elims: List[Elimination])
  case TCon(name: String, args: List[Term])
  case TLevel(level: Int)

  def tt(using ctx: NameContext) : TtTerm = this match {
    case TRedux(fn, elims) => TtTerm.TRedux(fn, elims.map(_.tt))
    case TFunction(arg, bodyTy) => TWhnf(WFunction(
      arg.name ∷ arg.ty.tt, 
      ctx.withName(arg.name) {
        bodyTy.tt
      }))
    case TVar(name, elims) => TWhnf(WVar(ctx(name), elims.map(_.tt)))
    case TCon(con, args) => TWhnf(WCon(con, args.map(_.tt)))
    case TLevel(level: Int) => TWhnf(WLevel(lconst(level)))
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
    case WUniverse(l) => TRedux(builtins.universeType.qn, List(ETerm(l.fe)))
    case WLevel(l) => l.fe
    case WLevelType => TRedux(builtins.levelType.qn, Nil)
    case WData(qn, params) => TRedux(qn, params.map(t => ETerm(t.fe)))
    case WRecord(qn, params) => TRedux(qn, params.map(t => ETerm(t.fe)))
    case WId(level, ty, left, right) => TRedux(builtins.idType.qn, List(ETerm(level.fe), ETerm(ty.fe), ETerm(left.fe), ETerm(right.fe)))
    case WVar(idx, elims) => TVar(ctx(idx), elims.map(_.fe))
    case WCon(con, args) => TCon(con, args.map(_.fe))
  }
}

extension levelFeOps on (self: Level) {
  def fe(using ctx: IndexedSeq[String]): Term = self match {
    case LVar(idx) => TVar(ctx(idx), Nil)
    case LConst(n) => TLevel(n)
    case LMax(l1, l2) => TRedux(builtins.lmaxFn.qn, List(ETerm(l1.fe), ETerm(l2.fe)))
    case LSuc(l) => TRedux(builtins.lsucFn.qn, List(ETerm(l.fe)))
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