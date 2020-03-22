package io.github.tgeng.stalker.core

enum Term {
  case TWhnf(whnf: Whnf)
  case TRedux(fn: QualifiedName, elims: List[Elimination])
}

enum Whnf {
  case WFunction(argTy: Term, bodyTy: Term)
  case WUniverse(level: Int)
  case WData(data: QualifiedName, params: List[Term])
  case WRecord(record: QualifiedName, params: List[Term])
  case WId(ty: Term, left: Term, right: Term)
  case WVar(idx: Int, elims: List[Elimination])
  case WCon(con: String, args: List[Term])
  case WRefl
}

enum Elimination {
  case ETerm(t: Term)
  case EProj(p: String)
}

import Term._
import Whnf._
import Elimination._

case class RaiseSpec(bar:Int, amount:Int)

extension termOps on (self: Term) {
  def raise(amount: Int) : Term = self.raiseImpl(using RaiseSpec(0, amount))

  def raiseImpl(using spec: RaiseSpec) : Term = self match {
    case TWhnf(whnf) => TWhnf(whnf.raiseImpl)
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.raiseImpl))
  }

  def substitute(substitution: Substitution[Term]) : Term = self.substituteImpl(using SubstituteSpec(0, substitution)).raise(-substitution.size)

  def substituteImpl(using spec: SubstituteSpec[Term]) : Term = self match {
    case TWhnf(whnf) => whnf.substituteImpl
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.substituteImpl))
  }
}

extension whnfOps on (self: Whnf) {
  def raiseImpl(using spec: RaiseSpec) : Whnf = self match {
    case WFunction(argTy, bodyTy) => WFunction(argTy.raiseImpl, bodyTy.raiseImpl(using RaiseSpec(spec.bar + 1, spec.amount)))
    case WUniverse(_) => self
    case WData(data, params) => WData(data, params.map(_.raiseImpl))
    case WRecord(record, params) => WRecord(record, params.map(_.raiseImpl))
    case WId(ty: Term, left: Term, right: Term) => WId(ty.raiseImpl, left.raiseImpl, right.raiseImpl)
    case WVar(idx, elims) => WVar(if(idx >= spec.bar) idx + 1 else idx, elims.map(_.raiseImpl))
    case WCon(con, args) => WCon(con, args.map(_.raiseImpl))
    case WRefl => WRefl
  }
  def substituteImpl(using spec: SubstituteSpec[Term]) : Term = self match {
    case WFunction(argTy, bodyTy) => TWhnf(WFunction(
      argTy.substituteImpl,
      bodyTy.substituteImpl(using SubstituteSpec(
        spec.offset + 1,
        spec.substitution.map(_.raise(1))))))
    case WUniverse(_) => TWhnf(self)
    case WData(data, params) => TWhnf(WData(data, params.map(_.substituteImpl)))
    case WRecord(record, params) => TWhnf(WRecord(record, params.map(_.substituteImpl)))
    case WId(ty, left, right) => TWhnf(WId(ty.substituteImpl, left.substituteImpl, right.substituteImpl))
    case WVar(idx, elims) =>
      if (idx >= spec.offset) (spec.substitution(idx - spec.offset), elims.isEmpty) match {
        case (_, true) => TWhnf(self)
        case (TWhnf(whnf), _) => whnf match {
          case WVar(idx, sElims) =>  TWhnf(WVar(idx, sElims ++ elims))
          case _ => throw IllegalArgumentException(s"Invalid substitution with $spec into $self")
        }
        case (TRedux(fn, sElims), _) => TRedux(fn, sElims ++ elims)
      } else
        TWhnf(WVar(idx, elims.map(_.substituteImpl)))
    case WCon(con, args) => TWhnf(WCon(con, args.map(_.substituteImpl)))
    case WRefl => TWhnf(self)
  }
}

extension eliminationOps on (self: Elimination) {
  def raiseImpl(using spec: RaiseSpec): Elimination = self match {
    case ETerm(t) => ETerm(t.raiseImpl)
    case EProj(p) => EProj(p)
  }
  def substituteImpl(using spec: SubstituteSpec[Term]) : Elimination = self match {
    case ETerm(t) => ETerm(t.substituteImpl)
    case EProj(p) => self
  }
}