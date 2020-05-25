package io.github.tgeng.stalker.core.tt

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Error._

type Type = Whnf

case class Binding[+T](ty: T)(val name: String) {
  override def toString = s"$name ∷ $ty"
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

  def app(t: Term): Result[Term] = app(Elimination.ETerm(t))
  def app(f: String): Result[Term] = app(Elimination.EProj(f))
  
  def app(e: Elimination) : Result[Term] = this match {
    case TRedux(fn, elims) => Right(TRedux(fn, elims :+ e))
    case TWhnf(Whnf.WVar(idx, elims)) => Right(TWhnf(Whnf.WVar(idx, elims :+ e)))
    case _ => typingError(s"Cannot apply $e to $this.")
  }

  def app(e̅: Seq[Elimination]) : Result[Term] = e̅.foldLeft[Result[Term]](Right(this))((acc, e) => acc.flatMap(_.app(e)))
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
  case WUniverse(level: Term)
  case WLevel(l: Int, maxOperands: Set[LSuc])
  case WLevelType
  case WData(qn: QualifiedName, params: List[Term])
  case WRecord(qn: QualifiedName, params: List[Term])
  case WId(level: Term, ty: Term, left: Term, right: Term)
  case WVar(idx: Int, elims: List[Elimination])
  case WCon(con: String, args: List[Term])

  def freeVars : Set[Int] = this match {
    case WFunction(arg, bodyTy) => arg.ty.freeVars | (bodyTy.freeVars &~ Set(0)).map(_ - 1)
    case WUniverse(l) => l.freeVars
    case WLevel(l, maxOperands) => maxOperands.flatMap{case LSuc(_, t) => t.freeVars}
    case WLevelType => Set.empty
    case WData(data, params) => params.flatMap(_.freeVars).toSet
    case WRecord(record, params) => params.flatMap(_.freeVars).toSet
    case WId(level, ty, left, right) => level.freeVars | ty.freeVars | left.freeVars | right.freeVars
    case WVar(idx, elims) => elims.flatMap(_.freeVars).toSet
    case WCon(con, args) => args.flatMap(_.freeVars).toSet
  }
}

case class LSuc(amount: Int, t: Term)

object Whnf {
  val WRefl : Whnf = WCon("Refl", Nil)
  def lmax(l1: Term, l2: Term) : WLevel = (l1, l2) match {
    case (TWhnf(WLevel(l1, mo1)), TWhnf(WLevel(l2, mo2))) => new WLevel(scala.math.max(l1, l2), mo1 | mo2)
    case (t, TWhnf(WLevel(l, mo))) => new WLevel(l, mo | Set(LSuc(0, t)))
    case (TWhnf(WLevel(l, mo)), t) => new WLevel(l, mo | Set(LSuc(0, t)))
    case (t1, t2) => new WLevel(0, Set(LSuc(0, t1), LSuc(0, t2)))
  }

  def lsuc(l: Term) : WLevel = l match {
    case (TWhnf(WLevel(l, mo))) => new WLevel(l+1, mo)
    case t => new WLevel(0, Set(LSuc(1, t)))
  }

  def lconst(i: Int) = WLevel(0, Set.empty)
}

given Raisable[Whnf] {
  def (w: Whnf) raiseImpl(using spec: RaiseSpec) : Whnf = w match {
    case WFunction(arg, bodyTy) => WFunction(arg.map(_.raiseImpl), bodyTy.raiseImpl(using spec.raised))
    case WUniverse(t) => WUniverse(t.raiseImpl)
    case WLevel(l, maxOperands) => WLevel(l, maxOperands.map{ case LSuc(a, t) => LSuc(a, t.raiseImpl)})
    case WLevelType => WLevelType
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
    case WUniverse(l) => TWhnf(WUniverse(l.substituteImpl))
    case WLevel(l, maxOperands) => TWhnf(WLevel(l, maxOperands.map{ case LSuc(a, t) => LSuc(a, t.substituteImpl)}))
    case WLevelType => TWhnf(WLevelType)
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
