package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._

case class FBinding(name: String, ty: FTerm)
type FTelescope = List[FBinding]

enum FTerm {
  case FTRedux(name: String, elims: List[FElimination])
  case FTFunction(arg: FBinding, bodyTy: FTerm)
  case FTCon(name: String, args: List[FTerm])
  case FTLevel(level: Int)
}

enum FElimination {
  case FETerm(t: FTerm)
  case FEProj(p: String)
}
