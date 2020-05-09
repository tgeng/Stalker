package io.github.tgeng.stalker.core.fe

import scala.collection.Seq
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.tt.Status

enum Declaration {
  case Data(qn: QualifiedName, paramTys: Telescope, level: Int, cons: Seq[Constructor])
  case Record(qn: QualifiedName, paramTys: Telescope, level: Int, fields: Seq[Field])
  case Definition(qn: QualifiedName, ty: Term, clauses: Seq[UncheckedClause])

  def qn: QualifiedName
}

import Declaration._

case class Constructor(name: String, argTys: Telescope)

case class Field(name: String, ty: Term)

case class UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs)

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}