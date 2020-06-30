package io.github.tgeng.stalker.core.tt

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.Error._
import io.github.tgeng.stalker.common.LocalNames

type Type = Whnf

case class Binding[+T](ty: T)(val name: String) {
  override def toString = s""""$name" ∷ $ty"""
}

extension stringBindingOps on [T](self: String) {
  def ∷ (t: T) = Binding(t)(self)
}

extension bindingOps on [T, R](self: Binding[T]) {
  def map(f: T => R) = Binding[R](f(self.ty))(self.name)
}

enum Term {
  case TWhnf(whnf: Whnf)
  case TRedux(fn: QualifiedName, elims: List[Elimination])

  def freeVars : Set[Int] = this match {
    case TWhnf(whnf) => whnf.freeVars
    case TRedux(fn, elims) => elims.flatMap(_.freeVars).toSet
  }

  override def toString : String = this match {
    case TWhnf(whnf) => s"""TWhnf($whnf)"""
    case TRedux(fn, elims) => s"""TRedux("$fn", $elims)"""
  }
}

given Raisable[Term] {
  def (t: Term) raiseImpl(using spec: RaiseSpec) : Term = t match {
    case TWhnf(whnf) => TWhnf(whnf.raiseImpl)
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.raiseImpl))
  }
}

given Substitutable[Term, Term, Term] {
  def (t: Term) substituteImpl(using spec: SubstituteSpec[Term]) : Term = t match {
    case TWhnf(whnf) => whnf.substituteImpl
    case TRedux(fn, elims) => TRedux(fn, elims.map(_.substituteImpl))
  }
}

import Term._

enum Whnf {
  case WFunction(arg: Binding[Term], bodyTy: Term)
  case WType(level: Term)
  case WLConst(l: Int)
  case WLMax(operands: Set[LSuc])
  case WLevel
  case WData(qn: QualifiedName, params: List[Term])
  case WRecord(qn: QualifiedName, params: List[Term])
  case WId(level: Term, ty: Term, left: Term, right: Term)
  case WVar(idx: Int, elims: List[Elimination])
  case WCon(con: String, args: List[Term])

  def freeVars : Set[Int] = this match {
    case WFunction(arg, bodyTy) => arg.ty.freeVars | (bodyTy.freeVars &~ Set(0)).map(_ - 1)
    case WType(l) => l.freeVars
    case WLConst(l) => Set.empty
    case WLMax(operands) => operands.flatMap{
      case LSuc(_, t) => t.freeVars
    }
    case WLevel => Set.empty
    case WData(data, params) => params.flatMap(_.freeVars).toSet
    case WRecord(record, params) => params.flatMap(_.freeVars).toSet
    case WId(level, ty, left, right) => level.freeVars | ty.freeVars | left.freeVars | right.freeVars
    case WVar(idx, elims) => Set(idx) | elims.flatMap(_.freeVars).toSet
    case WCon(con, args) => args.flatMap(_.freeVars).toSet
  }

  override def toString = this match {
    case WFunction(arg, bodyTy) => s"WFunction($arg, $bodyTy)"
    case WType(level) => s"WType($level)"
    case WLConst(l) => s"WLConst($l)"
    case WLMax(operands) => s"WLMax($operands)"
    case WLevel => "WLevel"
    case WData(qn, params) => s"""WData("$qn", $params)"""
    case WRecord(qn, params) => s"""WRecord("$qn", $params)"""
    case WId(level, ty, left, right) => s"WId($level, $ty, $left, $right)"
    case WVar(idx, elims) => s"WVar($idx, $elims)"
    case WCon(con, args) => s"""WCon("$con", $args)"""
  }
}

case class LSuc(amount: Int, t: Term)

object Whnf {
  val WRefl : Whnf = WCon("Refl", Nil)
  def lmax(l1: Term, l2: Term) : Whnf = (l1, l2) match {
    case (TWhnf(WLConst(l1)), TWhnf(WLConst(l2))) => WLConst(scala.math.max(l1, l2))
    case (TWhnf(WLMax(op1)), TWhnf(WLMax(op2))) => WLMax(op1 | op2)
    case (t, TWhnf(WLMax(op))) => WLMax(op | Set(LSuc(0, t)))
    case (TWhnf(WLMax(op)), t) => WLMax(op | Set(LSuc(0, t)))
    case (t1, t2) => WLMax(Set(LSuc(0, t1), LSuc(0, t2)))
  }

  def lsuc(l: Term) : Whnf = l match {
    case TWhnf(WLConst(l)) => WLConst(l + 1)
    case (TWhnf(WLMax(op))) => WLMax(op.map{
      case LSuc(l, t) => LSuc(l + 1, t)
    })
    case t => WLMax(Set(LSuc(1, t)))
  }

  def lconst(i: Int) = WLConst(i)
}

given Raisable[Whnf] {
  def (w: Whnf) raiseImpl(using spec: RaiseSpec) : Whnf = w match {
    case WFunction(arg, bodyTy) => WFunction(arg.map(_.raiseImpl), bodyTy.raiseImpl(using spec.raised))
    case WType(t) => WType(t.raiseImpl)
    case WLMax(op) => WLMax(op.map{ case LSuc(a, t) => LSuc(a, t.raiseImpl)})
    case WLConst(l) => WLConst(l)
    case WLevel => WLevel
    case WData(data, params) => WData(data, params.map(_.raiseImpl))
    case WRecord(record, params) => WRecord(record, params.map(_.raiseImpl))
    case WId(level, ty, left, right) => WId(level.raiseImpl, ty.raiseImpl, left.raiseImpl, right.raiseImpl)
    case WVar(idx, elims) => WVar(spec.trans(idx), elims.map(_.raiseImpl))
    case WCon(con, args) => WCon(con, args.map(_.raiseImpl))
  }
}

given Substitutable[Whnf, Term, Term] {
  def (w: Whnf) substituteImpl(using spec: SubstituteSpec[Term]) : Term = w match {
    case WFunction(arg, bodyTy) => TWhnf(WFunction(
      arg.map(_.substituteImpl),
      bodyTy.substituteImpl(using spec.raised)))
    case WType(l) => TWhnf(WType(l.substituteImpl))
    case WLMax(op) => TWhnf(WLMax(op.map{ case LSuc(a, t) => LSuc(a, t.substituteImpl)}))
    case WLConst(l) => TWhnf(WLConst(l))
    case WLevel => TWhnf(WLevel)
    case WData(data, params) => TWhnf(WData(data, params.map(_.substituteImpl)))
    case WRecord(record, params) => TWhnf(WRecord(record, params.map(_.substituteImpl)))
    case WId(level, ty, left, right) => TWhnf(WId(level.substituteImpl, ty.substituteImpl, left.substituteImpl, right.substituteImpl))
    case WVar(idx, elims) => spec.trans(idx) match {
      case Right(t) => (t, elims.map(_.substituteImpl)) match {
        case (s, Nil) => s
        case (TWhnf(WVar(idx, sElims)), elims) => TWhnf(WVar(idx, sElims ++ elims))
        case (TRedux(fn, sElims), elims) => TRedux(fn, sElims ++ elims)
        case _ => throw IllegalArgumentException(s"Invalid substitution with $spec into $w")
      }
      case Left(idx) => TWhnf(WVar(idx, elims.map(_.substituteImpl)))
    }
    case WCon(con, args) => TWhnf(WCon(con, args.map(_.substituteImpl)))
  }
}

import Whnf._

enum Elimination {
  case ETerm(t: Term)
  case EProj(p: String)
  
  def freeVars : Set[Int] = this match {
    case ETerm(t) => t.freeVars
    case EProj(p) => Set.empty
  }

  override def toString = this match {
    case ETerm(t) => s"ETerm($t)"
    case EProj(p) => s"""EProj("$p")"""
  }
}

given Raisable[Elimination] {
  def (e: Elimination) raiseImpl(using spec: RaiseSpec): Elimination = e match {
    case ETerm(t) => ETerm(t.raiseImpl)
    case EProj(p) => EProj(p)
  }
}

given Substitutable[Elimination, Term, Elimination] {
  def (e: Elimination) substituteImpl(using spec: SubstituteSpec[Term]) : Elimination = e match {
    case ETerm(t) => ETerm(t.substituteImpl)
    case EProj(p) => e
  }
}

import Elimination._
