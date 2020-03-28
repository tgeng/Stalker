package io.github.tgeng.stalker.core

import scala.language.implicitConversions

/** First element on the right. */
opaque type Substitution = IndexedSeq[*]

case class SubstituteSpec[T](offset: Int, substitution: Substitution[T])

extension substitutionOps on [T, R](self: Substitution[T]) {
  def get(idx: Int) = self(idx)
  def map(fn: T => R) : Substitution[R] = self.map(fn)
  def size = self.size
}

private def termsToSubstitution(terms: List[Term]) : Substitution[Term] = terms.reverse.toIndexedSeq
private def termToSubstitution(term: Term) : Substitution[Term] = IndexedSeq(term)

extension substitutionSpecTermOps on (self: SubstituteSpec[Term]) {
  def raised = SubstituteSpec(self.offset + 1, self.substitution.map(_.raise(1)))
}

object substitutionConversion {
  given termsToSubstitution as Conversion[List[Term], Substitution[Term]] = termsToSubstitution
  given termToSubstitution as Conversion[Term, Substitution[Term]] = termToSubstitution
}