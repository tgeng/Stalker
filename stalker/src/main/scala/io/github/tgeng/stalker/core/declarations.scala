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
  case UncheckedClause(lhs: Seq[CoPattern], rhs: UncheckedRhs) extends Clause[Unchecked]
  case CheckedClause(bindings: Telescope, lhs: Seq[CoPattern], rhs: Term, ty: Term) extends Clause[Checked]
}

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}

import Clause._

import scala.collection.mutable

type Signature[+C[_] <: scala.collection.IndexedSeq[_]] = C[Declaration[Checked, scala.collection.IndexedSeq]]