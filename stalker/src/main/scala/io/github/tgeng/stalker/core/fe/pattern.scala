package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.Namespace
import io.github.tgeng.stalker.common.Error._

enum FPattern {
  case FPVar(name: String)
  case FPCon(con: String, args: List[FPattern], forced: Boolean)
  case FPForced(t: FTerm)
  case FPAbsurd

  override def toString = this match {
    case FPVar(name) => s"""FPVar("$name")"""
    case FPCon(con, args, forced) => s"""FPCon("$con", $args, $forced)"""
    case FPForced(t) => s"FPForced($t)"
    case FPAbsurd => s"FPAbsurd"
  }
}

enum FCoPattern {
  case FQPattern(p: FPattern)
  case FQProj(p: String)

  override def toString = this match {
    case FQPattern(p) => s"FQPattern($p)"
    case FQProj(p) => s"""FQProj("$p")"""
  }
}
