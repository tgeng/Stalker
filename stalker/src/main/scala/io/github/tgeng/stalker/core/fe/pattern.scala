package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Binding => TtBinding, Term => TtTerm, Pattern => TtPattern, CoPattern => TtCoPattern}

enum Pattern {
  case PVar(name: String)
  case PRefl
  case PCon(con: String, patterns: List[Pattern])
  case PForcedCon(con: String, patterns: List[Pattern])
  case PForced(t: Term)
  case PAbsurd

  def tt(using ctx: NameContext) : Result[TtPattern] = this match {
    case PVar(name) => ctx.get(name).map(TtPattern.PVar(_)(name)) 
    case PRefl => Right(TtPattern.PRefl)
    case PCon(con, patterns) => patterns.liftMap(_.tt).map(TtPattern.PCon(con, _))
    case PForcedCon(con, patterns) => patterns.liftMap(_.tt).map(TtPattern.PForcedCon(con, _))
    case PForced(t) => t.tt.map(TtPattern.PForced(_))
    case PAbsurd => Right(TtPattern.PAbsurd)
  }

  def freeVars: Seq[String] = this match {
    case PVar(name) => Seq(name)
    case PRefl => Seq.empty
    case PCon(_, patterns) => patterns.flatMap(_.freeVars)
    case PForcedCon(_, patterns) => patterns.flatMap(_.freeVars)
    case PForced(_) => Seq.empty
    case PAbsurd => Seq.empty
  }
}

enum CoPattern {
  case QPattern(p: Pattern)
  case QProj(p: String)

  def tt(using ctx: NameContext) : Result[TtCoPattern] = this match {
    case QPattern(p) => p.tt.map(TtCoPattern.QPattern(_))
    case QProj(p) => Right(TtCoPattern.QProj(p))
  }

  def freeVars: Seq[String] = this match {
    case QPattern(p) => p.freeVars
    case QProj(_) => Seq.empty
  }
}
