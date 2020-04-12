package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import Term._
import Whnf._
import Elimination._
import substitutionConversion.{given _}

enum Pattern extends Raisable[Pattern] with Substitutable[Pattern, Pattern] {
  // A pattern is defined under a context containing all the (linear) free variables.
  // Since pattern construction does not introduce any bindings, 0 always points
  // to the rightmost (aka, first in context) variable. The context is generated
  // from the pattern, with the left most PVar bound to the leftmost (last in context)
  // binding in the context. Therefore, the left most PVar index is the biggest,
  // e.g. context.size - 1.
  case PVar(idx: Int)
  case PRefl
  case PCon(con: String, patterns: List[Pattern])
  case PForcedCon(con: String, patterns: List[Pattern])
  case PForced(t: Term)
  case PAbsurd

  def toTerm: Term = this match {
    case PVar(idx) => TWhnf(WVar(idx, Nil))
    case PRefl => TWhnf(WRefl)
    case PCon(con, patterns) => TWhnf(WCon(con, patterns.map(_.toTerm)))
    case PForcedCon(con, patterns) => TWhnf(WCon(con, patterns.map(_.toTerm)))
    case PForced(t) => t
    case PAbsurd => throw IllegalArgumentException()
  }

  def raiseImpl(using spec: RaiseSpec) : Pattern = this match {
    case PVar(idx) => PVar(spec.trans(idx))
    case PRefl => this
    case PCon(con, patterns) => PCon(con, patterns.map(_.raiseImpl))
    case PForcedCon(con, patterns) => PForcedCon(con, patterns.map(_.raiseImpl))
    case PForced(t) => PForced(t.raiseImpl)
    case PAbsurd => this
  }

  def substituteImpl(using spec: SubstituteSpec[Pattern]) : Pattern = this match {
    case PVar(idx) => spec.trans(idx) match {
      case Right(p) => p
      case Left(idx) => PVar(idx)
    }
    case PRefl => this
    case PCon(con, patterns) => PCon(con, patterns.map(_.substituteImpl))
    case PForcedCon(con, patterns) => PForcedCon(con, patterns.map(_.substituteImpl))
    case PForced(t) => PForced(t.substituteImpl(using spec))
    case PAbsurd => this
  }
}

import Pattern._

enum CoPattern extends Raisable[CoPattern] with Substitutable[Pattern, CoPattern] {
  case QPattern(p: Pattern)
  case QProj(p: String)

  def toElimination: Elimination = this match {
    case QPattern(p) => ETerm(p.toTerm)
    case QProj(p) => EProj(p)
  }

  def raiseImpl(using spec: RaiseSpec) : CoPattern = this match {
    case QPattern(p) => QPattern(p.raiseImpl)
    case QProj(_) => this
  }

  def substituteImpl(using spec: SubstituteSpec[Pattern]) : CoPattern = this match {
    case QPattern(p) => QPattern(p.substituteImpl)
    case QProj(_) => this
  }
}

import CoPattern._