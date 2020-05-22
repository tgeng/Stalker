package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._

enum FPattern {
  case FPVar(name: String)
  case FPCon(con: String, patterns: List[FPattern])
  case FPForcedCon(con: String, patterns: List[FPattern])
  case FPForced(t: FTerm)
  case FPAbsurd

  def freeVars: Seq[String] = this match {
    case FPVar(name) => Seq(name)
    case FPCon(_, patterns) => patterns.flatMap(_.freeVars)
    case FPForcedCon(_, patterns) => patterns.flatMap(_.freeVars)
    case FPForced(_) => Seq.empty
    case FPAbsurd => Seq.empty
  }
}

enum FCoPattern {
  case FQPattern(p: FPattern)
  case FQProj(p: String)

  def freeVars: Seq[String] = this match {
    case FQPattern(p) => p.freeVars
    case FQProj(_) => Seq.empty
  }
}
