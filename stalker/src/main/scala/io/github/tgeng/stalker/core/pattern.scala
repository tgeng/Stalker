package io.github.tgeng.stalker.core

import Term._
import Whnf._
import Elimination._

enum Pattern {
  case PVar(idx: Int)
  case PRefl
  case PCon(con: String, patterns: Seq[Pattern])
  case PForcedCon(con: String, patterns: Seq[Pattern])
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
    case PVar(idx) => TWhnf(WVar(idx, Seq.empty))
    case PRefl => TWhnf(WRefl)
    case PCon(con, patterns) => TWhnf(WCon(con, patterns.map(_.toTerm)))
    case PForcedCon(con, patterns) => TWhnf(WCon(con, patterns.map(_.toTerm)))
    case PForced(t) => t
    case PAbsurd => throw IllegalArgumentException()
  }
}

extension coPatternOps on (self: CoPattern) {
  def toElimination: Elimination = self match {
    case QPattern(p) => ETerm(p.toTerm)
    case QProj(p) => EProj(p)
  }
}
