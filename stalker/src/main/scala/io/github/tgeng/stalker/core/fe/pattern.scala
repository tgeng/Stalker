package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.tt.Namespace
import io.github.tgeng.stalker.core.common.Error._

enum FPattern {
  case FPVarCon(name: String)
  case FPCon(con: Seq[String] | String, args: List[FPattern], forced: Boolean)
  case FPForced(t: FTerm)
  case FPAbsurd

  override def toString = this match {
    case FPVarCon(name) => s"""FPVarCon("$name")"""
    case FPCon(con, args, forced) => s"""FPCon(${
      con match {
        case con : Seq[String] => con.map{ c => s""""$c""""}
        case con : String => s""""$con""""
      }
    }, $args, $forced)"""
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
