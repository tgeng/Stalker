package io.github.tgeng.stalker.core

import io.github.tgeng.stalker.common.QualifiedName

type Type = Whnf

enum Term extends Raisable[Term] with Substitutable[Term, Term] {
  case TWhnf(whnf: Whnf)
  case TRedux(fn: QualifiedName, elims: List[Elimination])

  def freeVars : Set[Int] = this match {
    case TWhnf(whnf) => whnf.freeVars
    case TRedux(fn, elims) => elims.flatMap(_.freeVars).toSet
  }

  def raiseImpl(using spec: RaiseSpec) : Term = this match {
    case TWhnf(whnf) => TWhnf(whnf.raiseImpl)
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.raiseImpl))
  }

  def substituteImpl(using spec: SubstituteSpec[Term]) : Term = this match {
    case TWhnf(whnf) => whnf.substituteImpl
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.substituteImpl))
  }

  def app(t: Term): Result[Term] = app(Elimination.ETerm(t))
  def app(f: String): Result[Term] = app(Elimination.EProj(f))
  
  def app(e: Elimination) : Result[Term] = this match {
    case TRedux(fn, elims) => Right(TRedux(fn, elims :+ e))
    case TWhnf(Whnf.WVar(idx, elims)) => Right(TWhnf(Whnf.WVar(idx, elims :+ e)))
    case _ => typingError(s"Cannot apply $e to $this.")
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

  def freeVars : Set[Int] = this match {
    case f@WFunction(argTy, bodyTy) => argTy.freeVars | (bodyTy.freeVars &~ Set(0)).map(_ - 1)
    case WUniverse(_) => Set.empty
    case WData(data, params) => params.flatMap(_.freeVars).toSet
    case WRecord(record, params) => params.flatMap(_.freeVars).toSet
    case WId(ty: Term, left: Term, right: Term) => ty.freeVars | left.freeVars | right.freeVars
    case WVar(idx, elims) => elims.flatMap(_.freeVars).toSet
    case WCon(con, args) => args.flatMap(_.freeVars).toSet
    case WRefl => Set.empty
  }


  def raiseImpl(using spec: RaiseSpec) : Whnf = this match {
    case f@WFunction(argTy, bodyTy) => WFunction(argTy.raiseImpl, bodyTy.raiseImpl(using spec.raised))(f.argName)
    case WUniverse(_) => this
    case WData(data, params) => WData(data, params.map(_.raiseImpl))
    case WRecord(record, params) => WRecord(record, params.map(_.raiseImpl))
    case WId(ty: Term, left: Term, right: Term) => WId(ty.raiseImpl, left.raiseImpl, right.raiseImpl)
    case WVar(idx, elims) => WVar(spec.trans(idx), elims.map(_.raiseImpl))
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
    case WVar(idx, elims) => spec.trans(idx) match {
      case Right(t) => (t, elims.map(_.substituteImpl)) match {
        case (s, Nil) => s
        case (TWhnf(WVar(idx, sElims)), elims) => TWhnf(WVar(idx, sElims ++ elims))
        case (TRedux(fn, sElims), elims) => TRedux(fn, sElims ++ elims)
        case _ => throw IllegalArgumentException(s"Invalid substitution with $spec into $this")
      }
      case Left(idx) => TWhnf(WVar(idx, elims.map(_.substituteImpl)))
    }
    case WCon(con, args) => TWhnf(WCon(con, args.map(_.substituteImpl)))
    case WRefl => TWhnf(this)
  }
}

import Whnf._

enum Elimination extends Raisable[Elimination] with Substitutable[Term, Elimination] {
  case ETerm(t: Term)
  case EProj(p: String)
  
  def freeVars : Set[Int] = this match {
    case ETerm(t) => t.freeVars
    case EProj(p) => Set.empty
  }

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