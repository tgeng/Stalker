package io.github.tgeng.stalker.core

import io.github.tgeng.common.indexedSeqOps._

case class Telescope(content: IndexedSeq[Term])

case class Context(content: IndexedSeq[Term])

case class Substitution(content: IndexedSeq[Term])

extension telescopeOps on (self: Telescope) {
  def +:(t: Term) = Telescope(t +: self.content)
  def :+(t: Term) = Telescope(self.content :+ t)
  def ++(other: Telescope) = Telescope(self.content ++ other.content)
  def toContext = Context(self.content)
  def apply(idx: Int) = self.content.lastN(idx)
}

extension contextOps on (self: Context) {
  def :+(t: Term) = Context(self.content :+ t)
  def ++(other: Telescope) = Context(self.content ++ other.content)
  def toTelescope = Telescope(self.content)
  def apply(idx: Int) = self.content.lastN(idx)
}

extension substitutionOps on (self: Substitution) {
  def ++(other: Substitution) = Substitution(self.content ++ other.content)
  def apply(idx: Int) = self.content.lastN(idx)
  def map(f : Term => Term) = Substitution(self.content.map(f))
}