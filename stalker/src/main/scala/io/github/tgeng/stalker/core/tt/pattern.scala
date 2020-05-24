package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.common.error._
import Term._
import Whnf._
import Elimination._
import substitutionConversion.{given _}

enum Pattern {
  // A pattern is defined under a context containing all the (linear) free variables.
  // Since pattern construction does not introduce any bindings, 0 always points
  // to the rightmost (aka, first in context) variable. The context is generated
  // from the pattern, with the left most PVar bound to the leftmost (last in context)
  // binding in the context. Therefore, the left most PVar index is the biggest,
  // e.g. context.size - 1.
  case PVar(idx: Int)(val name: String)
  case PCon(con: String, args: List[Pattern])
  case PForcedCon(con: String, args: List[Pattern])
  case PForced(t: Term)
  case PAbsurd

  def toTerm: Term = this match {
    case PVar(idx) => TWhnf(WVar(idx, Nil))
    case PCon(con, args) => TWhnf(WCon(con, args.map(_.toTerm)))
    case PForcedCon(con, args) => TWhnf(WCon(con, args.map(_.toTerm)))
    case PForced(t) => t
    case PAbsurd => throw IllegalArgumentException()
  }
}

object Pattern {
  val PRefl : Pattern = PCon("Refl", Nil)
}

given Raisable[Pattern] {
  def (p: Pattern) raiseImpl(using spec: RaiseSpec) : Pattern = p match {
    case p@PVar(idx) => PVar(spec.trans(idx))(p.name)
    case PCon(con, patterns) => PCon(con, patterns.map(_.raiseImpl))
    case PForcedCon(con, patterns) => PForcedCon(con, patterns.map(_.raiseImpl))
    case PForced(t) => PForced(t.raiseImpl)
    case PAbsurd => p
  }
}

given Substitutable[Pattern, Pattern, Pattern] {
  def (p: Pattern) substituteImpl(using spec: SubstituteSpec[Pattern]) : Pattern = p match {
    case p@PVar(idx) => spec.trans(idx) match {
      case Right(p) => p
      case Left(idx) => PVar(idx)(p.name)
    }
    case PCon(con, patterns) => PCon(con, patterns.map(_.substituteImpl))
    case PForcedCon(con, patterns) => PForcedCon(con, patterns.map(_.substituteImpl))
    case PForced(t) => PForced(t.substituteImpl(using spec))
    case PAbsurd => p
  }
}

import Pattern._

enum CoPattern {
  case QPattern(p: Pattern)
  case QProj(p: String)

  def toElimination: Elimination = this match {
    case QPattern(p) => ETerm(p.toTerm)
    case QProj(p) => EProj(p)
  }
}

given Raisable[CoPattern] {
  def (q: CoPattern) raiseImpl(using spec: RaiseSpec) : CoPattern = q match {
    case QPattern(p) => QPattern(p.raiseImpl)
    case QProj(_) => q
  }
}

given Substitutable[CoPattern, Pattern, CoPattern] {
  def (q: CoPattern) substituteImpl(using spec: SubstituteSpec[Pattern]) : CoPattern = q match {
    case QPattern(p) => QPattern(p.substituteImpl)
    case QProj(_) => q
  }
}

import CoPattern._