package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.common.LocalTfCtx
import scala.collection.mutable.ArrayBuffer

/** First element on the right. */
opaque type Context = List[Binding[Type]]

object Context {
  val empty : Context = Nil
  def from(content : Seq[Binding[Type]]) : Context = content.toList
}

extension contextOps on (self: Context) {
  def toTelescope : Telescope = self.reverse
  def toList : List[Binding[Type]] = self

  def splitAt(idx: Int) : (Context, Binding[Type], Telescope) = (self.slice(idx + 1, self.size), self(idx), self.slice(0, idx).reverse)

  def + (ty: Binding[Type]) : Context = ty +: self
  def + (tys: Telescope) : Context = tys.reverse ++ self

  def apply(idx : Int) : Binding[Type] = self(idx).map(_.raise(idx + 1))
  def size = self.size

  def toClosedTelescope : List[Binding[Type]] = self.reverse

  def toLocalTfCtx = LocalTfCtx(ArrayBuffer[String](self.map(_.name) : _*))
}
