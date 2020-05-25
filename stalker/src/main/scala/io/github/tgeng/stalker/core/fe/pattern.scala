package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.Error._

enum FPattern {
  case FPVar(name: String)
  case FPCon(con: String, args: List[FPattern])
  case FPForcedCon(con: String, args: List[FPattern])
  case FPForced(t: FTerm)
  case FPAbsurd

  def freeVars: Seq[String] = this match {
    case FPVar(name) => Seq(name)
    case FPCon(_, args) => args.flatMap(_.freeVars)
    case FPForcedCon(_, args) => args.flatMap(_.freeVars)
    case FPForced(_) => Seq.empty
    case FPAbsurd => Seq.empty
  }
}

enum FCoPattern {
  case FQPattern(p: FPattern)
  case FQProj(p: String)

  def freeVars(using ns: Namespace): Seq[String] = this match {
    case FQPattern(p) => p.freeVars
    case FQProj(_) => Seq.empty
  }
}
