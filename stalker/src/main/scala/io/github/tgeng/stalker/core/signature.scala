package io.github.tgeng.stalker.core

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum Declaration[S <: Status, +C[_] <: scala.collection.IndexedSeq[_]] {
  case Data(qn: QualifiedName, params: Telescope, level: Int, cons: C[Constructor])
  case Record(qn: QualifiedName, params: Telescope, level: Int, fields: C[Field])
  case Definition(qn: QualifiedName, ty: Term, clauses: C[Clause[S]])
}

import Declaration._

case class Constructor(name: String, args: Telescope)

case class Field(name: String, ty: Term)

enum Clause[T <: Status] {
  case UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs) extends Clause[Unchecked]
  case CheckedClause(bindings: Telescope, lhs: List[CoPattern], rhs: Term, ty: Term) extends Clause[Checked]
}

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}

import Clause._

import scala.collection.mutable

type SignatureT[+C[_] <: scala.collection.IndexedSeq[_]] = C[Declaration[Checked, scala.collection.IndexedSeq]]
type Signature = SignatureT[scala.collection.IndexedSeq]