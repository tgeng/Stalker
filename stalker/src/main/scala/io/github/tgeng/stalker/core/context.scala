package io.github.tgeng.stalker.core

import scala.language.implicitConversions

/** First element on the right. */
opaque type Context = List[Binding[Type]]

object Context {
  val empty : Context = Nil
  def from(content : Seq[Binding[Type]]) : Context = content.toList
}

extension contextOps on (self: Context) {
  def toTelescope : Telescope = self.reverse

  def splitAt(idx: Int) : (Context, Binding[Type], Telescope) = (self.slice(idx + 1, self.size), self(idx), self.slice(0, idx).reverse)

  def + (ty: Binding[Type]) : Context = ty +: self
  def + (tys: Telescope) : Context = tys.reverse ++ self

  def apply(idx : Int) : Binding[Type] = self(idx).map(_.raise(idx + 1))
  def size = self.size
  // def idSubst(using Γ:Context) : Substitution[Pattern] = {
  //   val startingIndex = Γ.size - self.size
  //   Substitution(Γ.size, (0 until self.size).map(i => Pattern.PVar(i + startingIndex)))
  // }
}
