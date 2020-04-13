package io.github.tgeng.stalker.core

import scala.language.implicitConversions

/** First element on the right. */
opaque type Context = List[Binding[Type]]

object Context {
  val empty : Context = Nil
}

extension contextOps on (self: Context) {
  def toTelescope : Telescope = self.reverse

  def splitAt(idx: Int) : (Context, Binding[Type], Telescope) = (self.slice(idx + 1, self.size), self(idx), self.slice(0, idx).reverse)

  def + (ty: Binding[Type]) : Context = ty :: self
  def + (tys: Telescope) : Context = tys.reverse ++ self

  def apply(idx : Int) = self(idx).map(_.raise(idx + 1))
  def size = self.size
}