package io.github.tgeng.stalker.core

import scala.collection.Map
import scala.collection.IndexedSeq

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum DeclarationT[S <: Status, +C[_] <: IndexedSeq[_]] {
  case DataT(qn: QualifiedName, paramTys: Telescope, level: Int, cons: C[Constructor])
  case RecordT(qn: QualifiedName, paramsTys: Telescope, level: Int, fields: C[Field])
  case DefinitionT(qn: QualifiedName, ty: Type, clauses: List[Clause[S]])
}

import DeclarationT._

case class Constructor(name: String, argTys: Telescope)

case class Field(name: String, ty: Type)

enum Clause[T <: Status] {
  case UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs) extends Clause[Unchecked]
  case CheckedClause(bindings: Telescope, lhs: List[CoPattern], rhs: Term, ty: Type) extends Clause[Checked]
}

import Clause._

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}

import UncheckedRhs._

type Declaration = DeclarationT[Checked, IndexedSeq]
type Data = DataT[Checked, IndexedSeq]
type Record = RecordT[Checked, IndexedSeq]
type Definition = DefinitionT[Checked, IndexedSeq]

type Signature = Map[QualifiedName, Declaration]