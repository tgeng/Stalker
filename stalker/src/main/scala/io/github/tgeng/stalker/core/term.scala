package io.github.tgeng.stalker.core

enum Term {
  case TWhnf(whnf: Whnf)
  case TRedux(fn: QualifiedName, elims: Seq[Elimination])
}

enum Whnf {
  case WFunction(argTy: Term, bodyTy: Term)
  case WUniverse(level: Int)
  case WData(data: QualifiedName, params: Seq[Term])
  case WRecord(record: QualifiedName, params: Seq[Term])
  case WId(ty: Term, left: Term, right: Term)
  case WVar(idx: Int, elims: Seq[Elimination])
  case WCon(con: String, args: Seq[Term])
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

case class SubstituteSpec(offset: Int, substitution: Substitution)

extension termOps on (self: Term) {
  def raise(using spec: RaiseSpec) : Term = self match {
    case TWhnf(whnf) => TWhnf(whnf.raise)
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.raise))
  }

  def substitute(using spec: SubstituteSpec) : Term = self match {
    case TWhnf(whnf) => whnf.substitute
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.substitute))
  }
}

extension whnfOps on (self: Whnf) {
  def raise(using spec: RaiseSpec) : Whnf = self match {
    case WFunction(argTy, bodyTy) => WFunction(argTy.raise, bodyTy.raise(using RaiseSpec(spec.bar + 1, spec.amount)))
    case WUniverse(_) => self
    case WData(data, params) => WData(data, params.map(_.raise))
    case WRecord(record, params) => WRecord(record, params.map(_.raise))
    case WId(ty: Term, left: Term, right: Term) => WId(ty.raise, left.raise, right.raise)
    case WVar(idx, elims) => WVar(if(idx >= spec.bar) idx + 1 else idx, elims.map(_.raise))
    case WCon(con, args) => WCon(con, args.map(_.raise))
    case WRefl => WRefl
  }
  def substitute(using spec: SubstituteSpec) : Term = self match {
    case WFunction(argTy, bodyTy) => TWhnf(WFunction(
      argTy.substitute,
      bodyTy.substitute(using SubstituteSpec(
        spec.offset + 1,
        spec.substitution.map(_.raise(using RaiseSpec(0, 1)))))))
    case WUniverse(_) => TWhnf(self)
    case WData(data, params) => TWhnf(WData(data, params.map(_.substitute)))
    case WRecord(record, params) => TWhnf(WRecord(record, params.map(_.substitute)))
    case WId(ty, left, right) => TWhnf(WId(ty.substitute, left.substitute, right.substitute))
    case WVar(idx, elims) =>
      if (idx >= spec.offset) (spec.substitution(idx - spec.offset), elims.isEmpty) match {
        case (_, true) => TWhnf(self)
        case (TWhnf(whnf), _) => whnf match {
          case WVar(idx, sElims) =>  TWhnf(WVar(idx, sElims ++ elims))
          case _ => throw IllegalArgumentException(s"Invalid substitution with $spec into $self")
        }
        case (TRedux(fn, sElims), _) => TRedux(fn, sElims ++ elims)
      } else
        TWhnf(WVar(idx, elims.map(_.substitute)))
  }
}

extension eliminationOps on (self: Elimination) {
  def raise(using spec: RaiseSpec): Elimination = self match {
    case ETerm(t) => ETerm(t.raise)
    case EProj(p) => EProj(p)
  }
  def substitute(using spec: SubstituteSpec) : Elimination = self match {
    case ETerm(t) => ETerm(t.substitute)
    case EProj(p) => self
  }
}