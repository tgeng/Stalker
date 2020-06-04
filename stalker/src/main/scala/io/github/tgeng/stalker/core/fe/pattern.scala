package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.Error._

enum FPattern {
  case FPVarCon(name: String)
  case FPCon(con: Seq[String], args: List[FPattern])
  case FPForcedCon(con: String, args: List[FPattern])
  case FPForced(t: FTerm)
  case FPAbsurd
}

enum FCoPattern {
  case FQPattern(p: FPattern)
  case FQProj(p: String)
}
