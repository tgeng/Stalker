package io.github.tgeng.stalker.frontend

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.signatureBuilder._
import io.github.tgeng.stalker.core.Status
import Status._

enum DeclarationT[S <: Status, +C[_]] {
  case DataT(qn: QualifiedName, paramTys: Telescope, level: Int, cons: C[Constructor])
  case RecordT(qn: QualifiedName, paramTys: Telescope, level: Int, fields: C[Field])
  case DefinitionT(qn: QualifiedName, ty: Term, clauses: C[Clause[S]])
}

import DeclarationT._

case class Constructor(name: String, argTys: Telescope)

case class Field(name: String, ty: Term)

enum Clause[T <: Status] {
  case UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs) extends Clause[Unchecked]
  case CheckedClause(bindings: Telescope, lhs: List[CoPattern], rhs: Term, ty: Term)
}

import Clause._

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}