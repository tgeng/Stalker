package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import io.github.tgeng.common.indexedSeqOps._
import substitutionOps._

case class Binding[T](ty: T)(val name: String)

extension bindingOps on [T, R](self: Binding[T]) {
  def map(f: T => R) = Binding[R](f(self.ty))(self.name)
}

/** First element on the left. */
type Telescope = List[Binding[Type]]

/** First element on the right. */
type Context = List[Type]

extension telescopeOps on (self: Telescope) {
  def toContext = self.reverse.map(_.ty)
  def apply(s: Substitution[Term])(using Γ: Context)(using Σ: Signature) = self.substituteImpl(
    using SubstituteSpec(0, s.map(_.raise(s.size))))
    .map(_.map(_.raise(-s.size)))
  def substituteImpl(using spec: SubstituteSpec[Term])(using Γ: Context)(using Σ: Signature) : List[Binding[Term]] = self match {
    case Nil => Nil
    case ty :: rest => ty.map(_.substituteImpl) :: rest.substituteImpl(using spec.raised)
  }
}
