package io.github.tgeng.stalker.core

import Term._
import Whnf._
import Elimination._
import substitutionOps._

enum Pattern {
  case PVar(idx: Int)
  case PRefl
  case PCon(con: String, patterns: List[Pattern])
  case PForcedCon(con: String, patterns: List[Pattern])
  case PForced(t: Term)
  case PAbsurd
}

enum CoPattern {
  case QPattern(p: Pattern)
  case QProj(p: String)
}

import Pattern._
import CoPattern._

extension patternOps on (self: Pattern) {
  def toTerm: Term = self match {
    case PVar(idx) => TWhnf(WVar(idx, Nil))
    case PRefl => TWhnf(WRefl)
    case PCon(con, patterns) => TWhnf(WCon(con, patterns.map(_.toTerm)))
    case PForcedCon(con, patterns) => TWhnf(WCon(con, patterns.map(_.toTerm)))
    case PForced(t) => t
    case PAbsurd => throw IllegalArgumentException()
  }

  def substituteImpl(using spec: SubstituteSpec[Pattern]) : Pattern = self match {
    case PVar(idx) => if (idx >= spec.offset) spec.substitution.get(idx - spec.offset) else self
    case PRefl => self
    case PCon(con, patterns) => PCon(con, patterns.map(_.substituteImpl))
    case PForcedCon(con, patterns) => PForcedCon(con, patterns.map(_.substituteImpl))
    case PForced(t) => PForced(t(spec.substitution.map(_.toTerm)))
    case PAbsurd => self
  }
}

extension coPatternOps on (self: CoPattern) {
  def toElimination: Elimination = self match {
    case QPattern(p) => ETerm(p.toTerm)
    case QProj(p) => EProj(p)
  }
}
