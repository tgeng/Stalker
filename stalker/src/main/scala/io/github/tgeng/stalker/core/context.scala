package io.github.tgeng.stalker.core

import io.github.tgeng.common.indexedSeqOps._

type Telescope = List[Type]

type Context = List[Type]

case class Substitution[T](content: IndexedSeq[T])

case class SubstituteSpec[T](offset: Int, substitution: Substitution[T])

extension telescopeOps on (self: Telescope) {
  def toContext = self.reverse
}

extension contextOps on (self: Context) {
  def toTelescope : Telescope = self.reverse
}

extension substitutionOps on [T, R](self: Substitution[T]) {
  def ++(other: Substitution[T]) = Substitution(self.content ++ other.content)
  def apply(idx: Int) = self.content.lastN(idx)
  def map(f : T => R) = Substitution[R](self.content.map(f))
  def size = self.content.size
}