package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.Error._
import pprint.{given _, _}

case class FBinding(name: String, ty: FTerm) {
  override def toString = s"""FBinding("$name", $ty)"""
}
type FTelescope = List[FBinding]

enum FTerm {
  case FTFunction(arg: FBinding, bodyTy: FTerm)
  case FTCon(name: String, args: List[FTerm])
  case FTLevel(level: Int)
  case FTRedux(names: List[String], elims: List[FElimination])
  case FTNat(n: Int)

  override def toString = this match {
    case FTFunction(arg, bodyTy) => s"FTFunction($arg, $bodyTy)"
    case FTCon(name, args) => s"""FTCon("$name", $args)"""
    case FTLevel(level) => s"""FTLevel($level)"""
    case FTRedux(names, elims) => s"""FTRedux(${names.map(name => s""""$name"""")}, $elims)"""
    case FTNat(n) => s"FTNat($n)"
  }
}

enum FElimination {
  case FETerm(t: FTerm)
  case FEProj(p: String)

  override def toString = this match {
    case FETerm(t) => s"FETerm($t)"
    case FEProj(p) => s"""FEProj("$p")"""
  }
}
