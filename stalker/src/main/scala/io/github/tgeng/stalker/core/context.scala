package io.github.tgeng.stalker.core

import scala.language.implicitConversions

/** First element on the right. */
opaque type Context = IndexedSeq[Binding[Type]]

object Context {
  val empty : Context = IndexedSeq.empty
}

extension contextOps on (self: Context) {
  def toTelescope : Telescope = self.reverse.toList

  def splitAt(idx: Int) : (Context, Binding[Type], Telescope) = (self.slice(idx + 1, self.size), self(idx), self.slice(0, idx).reverse.toList)

  def + (ty: Binding[Type]) : Context = ty +: self
  def + (tys: Telescope) : Context = tys.reverse.toIndexedSeq ++ self

  def apply(idx : Int) = self(idx).map(_.raise(idx + 1))
  def size = self.size
  def idSubst : Substitution[Pattern] = Substitution(self.size, (0 until self.size).map(Pattern.PVar(_)))
}