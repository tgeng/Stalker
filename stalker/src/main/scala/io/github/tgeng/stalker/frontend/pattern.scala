package io.github.tgeng.stalker.frontend

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.{Binding => DbBinding, Term => DbTerm}

enum Pattern {
  case PVar(name: String)
  case PRefl
  case PCon(con: String, patterns: List[Pattern])
  case PForcedCon(con: String, patterns: List[Pattern])
  case PForced(t: Term)
  case PAbsurd
}

enum CoPattern {
  case QPattern(p: Pattern)
  case QProj(p: String)
}