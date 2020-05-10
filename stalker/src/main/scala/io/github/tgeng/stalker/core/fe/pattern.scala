package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Binding => DbBinding, Term => DbTerm, Pattern => DbPattern, CoPattern => DbCoPattern}

enum Pattern {
  case PVar(name: String)
  case PRefl
  case PCon(con: String, patterns: List[Pattern])
  case PForcedCon(con: String, patterns: List[Pattern])
  case PForced(t: Term)
  case PAbsurd

  def tt(using ctx: NameContext) : Result[DbPattern] = this match {
    case PVar(name) => ctx.get(name).map(DbPattern.PVar(_)) 
    case PRefl => Right(DbPattern.PRefl)
    case PCon(con, patterns) => patterns.liftMap(_.tt).map(DbPattern.PCon(con, _))
    case PForcedCon(con, patterns) => patterns.liftMap(_.tt).map(DbPattern.PForcedCon(con, _))
    case PForced(t) => t.tt.map(DbPattern.PForced(_))
    case PAbsurd => Right(DbPattern.PAbsurd)
  }
}

enum CoPattern {
  case QPattern(p: Pattern)
  case QProj(p: String)

  def tt(using ctx: NameContext) : Result[DbCoPattern] = this match {
    case QPattern(p) => p.tt.map(DbCoPattern.QPattern(_))
    case QProj(p) => Right(DbCoPattern.QProj(p))
  }
}
