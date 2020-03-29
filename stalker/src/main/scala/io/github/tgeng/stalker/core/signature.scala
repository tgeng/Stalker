package io.github.tgeng.stalker.core

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum DeclarationT[S <: Status, +C[_] <: scala.collection.IndexedSeq[_]] {
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

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}

import Clause._

import scala.collection.mutable

type SignatureT[+C[_] <: scala.collection.IndexedSeq[_]] = C[DeclarationT[Checked, scala.collection.IndexedSeq]]

type Signature = Map[QualifiedName, DeclarationT[Checked, IndexedSeq]]
type Declaration = DeclarationT[Checked, IndexedSeq]
import DeclarationT._
type Data = DataT[Checked, IndexedSeq]
type Record = RecordT[Checked, IndexedSeq]
type Definition = DefinitionT[Checked, IndexedSeq]