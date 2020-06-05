package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.Error._

enum FPattern {
  case FPVarCon(name: String)
  case FPCon(con: Seq[String], args: List[FPattern])
  case FPForcedCon(con: Seq[String], args: List[FPattern])
  case FPForced(t: FTerm)
  case FPAbsurd

  override def toString = this match {
    case FPVarCon(name) => s"""FPVarCon("$name")"""
    case FPCon(con, args) => s"""FPCon(${con.map{ c => '"' + c + '"'}}, $args)"""
    case FPForcedCon(con, args) => s"""FPForcedCon(${con.map{ c => '"' + c + '"'}}, $args)"""
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
