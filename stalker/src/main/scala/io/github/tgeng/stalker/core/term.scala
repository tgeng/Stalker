package io.github.tgeng.stalker.core

import io.github.tgeng.stalker.common.QualifiedName

type Type = Whnf

enum Term extends Raisable[Term] with Substitutable[Term, Term] {
  case TWhnf(whnf: Whnf)
  case TRedux(fn: QualifiedName, elims: List[Elimination])

  def raiseImpl(using spec: RaiseSpec) : Term = this match {
    case TWhnf(whnf) => TWhnf(whnf.raiseImpl)
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.raiseImpl))
  }

  def substituteImpl(using spec: SubstituteSpec[Term]) : Term = this match {
    case TWhnf(whnf) => whnf.substituteImpl
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.substituteImpl))
  }
}

import Term._

enum Whnf extends Raisable[Whnf] with Substitutable[Term, Term] {
  case WFunction(argTy: Term, bodyTy: Term)(val argName: String)
  case WUniverse(level: Int)
  case WData(qn: QualifiedName, params: List[Term])
  case WRecord(qn: QualifiedName, params: List[Term])
  case WId(ty: Term, left: Term, right: Term)
  case WVar(idx: Int, elims: List[Elimination])
  case WCon(con: String, args: List[Term])
  case WRefl

  def raiseImpl(using spec: RaiseSpec) : Whnf = this match {
    case f@WFunction(argTy, bodyTy) => WFunction(argTy.raiseImpl, bodyTy.raiseImpl(using RaiseSpec(spec.bar + 1, spec.amount)))(f.argName)
    case WUniverse(_) => this
    case WData(data, params) => WData(data, params.map(_.raiseImpl))
    case WRecord(record, params) => WRecord(record, params.map(_.raiseImpl))
    case WId(ty: Term, left: Term, right: Term) => WId(ty.raiseImpl, left.raiseImpl, right.raiseImpl)
    case WVar(idx, elims) => WVar(if(idx >= spec.bar) idx + 1 else idx, elims.map(_.raiseImpl))
    case WCon(con, args) => WCon(con, args.map(_.raiseImpl))
    case WRefl => WRefl
  }

  def substituteImpl(using spec: SubstituteSpec[Term]) : Term = this match {
    case f@WFunction(argTy, bodyTy) => TWhnf(WFunction(
      argTy.substituteImpl,
      bodyTy.substituteImpl(using spec.raised))(f.argName))
    case WUniverse(_) => TWhnf(this)
    case WData(data, params) => TWhnf(WData(data, params.map(_.substituteImpl)))
    case WRecord(record, params) => TWhnf(WRecord(record, params.map(_.substituteImpl)))
    case WId(ty, left, right) => TWhnf(WId(ty.substituteImpl, left.substituteImpl, right.substituteImpl))
    case WVar(idx, elims) =>
      if (idx >= spec.offset) (spec.substitution.get(idx - spec.offset), elims) match {
        case (s, Nil) => s
        case (TWhnf(WVar(idx, sElims)), _) => TWhnf(WVar(idx, sElims ++ elims.map(_.substituteImpl)))
        case (TRedux(fn, sElims), _) => TRedux(fn, sElims ++ elims.map(_.substituteImpl))
        case _ => throw IllegalArgumentException(s"Invalid substitution with $spec into $this")
      } else
        TWhnf(WVar(idx + spec.substitution.sourceContextSize, elims.map(_.substituteImpl)))
    case WCon(con, args) => TWhnf(WCon(con, args.map(_.substituteImpl)))
    case WRefl => TWhnf(this)
  }
}

import Whnf._

enum Elimination extends Raisable[Elimination] with Substitutable[Term, Elimination] {
  case ETerm(t: Term)
  case EProj(p: String)

  def raiseImpl(using spec: RaiseSpec): Elimination = this match {
    case ETerm(t) => ETerm(t.raiseImpl)
    case EProj(p) => EProj(p)
  }
  def substituteImpl(using spec: SubstituteSpec[Term]) : Elimination = this match {
    case ETerm(t) => ETerm(t.substituteImpl)
    case EProj(p) => this
  }
}

import Elimination._