package io.github.tgeng.stalker.core

import io.github.tgeng.common.indexedSeqOps._

type Telescope = List[Term]

case class Context(content: IndexedSeq[Term])

case class Substitution[T](content: IndexedSeq[T])

case class SubstituteSpec[T](offset: Int, substitution: Substitution[T])

extension telescopeOps on (self: Telescope) {
  def toContext = Context(self.toIndexedSeq)
}

extension contextOps on (self: Context) {
  def :+(t: Term) = Context(self.content :+ t)
  def ++(other: Telescope) = Context(self.content ++ other)
  def apply(idx: Int) = self.content.lastN(idx)
}

extension substitutionOps on [T, R](self: Substitution[T]) {
  def ++(other: Substitution[T]) = Substitution(self.content ++ other.content)
  def apply(idx: Int) = self.content.lastN(idx)
  def map(f : T => R) = Substitution[R](self.content.map(f))
  def size = self.content.size
}