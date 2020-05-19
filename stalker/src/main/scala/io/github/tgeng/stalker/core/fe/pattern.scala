package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Binding => TtBinding, Term => TtTerm, Pattern => TtPattern, CoPattern => TtCoPattern}

enum Pattern {
  case PVar(name: String)
  case PCon(con: String, patterns: List[Pattern])
  case PForcedCon(con: String, patterns: List[Pattern])
  case PForced(t: Term)
  case PAbsurd

  def tt(using ctx: NameContext) : TtPattern = this match {
    case PVar(name) => TtPattern.PVar(ctx(name))(name)
    case PCon(con, patterns) => TtPattern.PCon(con, patterns.map(_.tt))
    case PForcedCon(con, patterns) => TtPattern.PForcedCon(con, patterns.map(_.tt))
    case PForced(t) => TtPattern.PForced(t.tt)
    case PAbsurd => TtPattern.PAbsurd
  }

  def freeVars: Seq[String] = this match {
    case PVar(name) => Seq(name)
    case PCon(_, patterns) => patterns.flatMap(_.freeVars)
    case PForcedCon(_, patterns) => patterns.flatMap(_.freeVars)
    case PForced(_) => Seq.empty
    case PAbsurd => Seq.empty
  }
}

enum CoPattern {
  case QPattern(p: Pattern)
  case QProj(p: String)

  def tt(using ctx: NameContext) : TtCoPattern = this match {
    case QPattern(p) => TtCoPattern.QPattern(p.tt)
    case QProj(p) => TtCoPattern.QProj(p)
  }

  def freeVars: Seq[String] = this match {
    case QPattern(p) => p.freeVars
    case QProj(_) => Seq.empty
  }
}
