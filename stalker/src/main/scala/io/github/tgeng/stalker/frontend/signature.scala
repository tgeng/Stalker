package io.github.tgeng.stalker.frontend

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.Status

enum Declaration {
  case Data(qn: QualifiedName, paramTys: Telescope, level: Int, cons: ArrayBuffer[Constructor])
  case Record(qn: QualifiedName, paramTys: Telescope, level: Int, fields: ArrayBuffer[Field])
  case Definition(qn: QualifiedName, ty: Term, clauses: ArrayBuffer[UncheckedClause])
}

import Declaration._

case class Constructor(name: String, argTys: Telescope)

case class Field(name: String, ty: Term)

case class UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs)

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}