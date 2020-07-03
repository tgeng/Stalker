package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import scala.collection.Seq
import io.github.tgeng.common.eitherOps._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.stalker.common.Error._
import io.github.tgeng.stalker.common.Namespace
import io.github.tgeng.stalker.core.tt._


enum FDeclaration {
  case FData(name: String, paramTys: FTelescope, ty: FTerm, cons: Seq[FConstructor])
  case FRecord(name: String, paramTys: FTelescope, ty: FTerm, fields: Seq[FField])
  case FDefinition(name: String, ty: FTerm, clauses: Seq[FUncheckedClause])

  override def toString = this match {
    case FData(name, paramTys ,ty, cons) => s"""FData("$name", $paramTys, $ty, $cons)"""
    case FRecord(name, paramTys ,ty, fields) => s"""FRecord("$name", $paramTys, $ty, $fields)"""
    case FDefinition(name, ty, clauses) => s"""FDefinition("$name", $ty, $clauses)"""
  }

  def name: String
}

case class FConstructor(name: String, argTys: FTelescope) {
  override def toString = s"""FConstructor("$name", $argTys)"""
}

case class FField(name: String, ty: FTerm) {
  override def toString = s"""FField("$name", $ty)"""
}

case class FUncheckedClause(lhs: List[FCoPattern], rhs: FUncheckedRhs)

enum FUncheckedRhs {
  case FUTerm(t: FTerm)
  case FUImpossible
}
