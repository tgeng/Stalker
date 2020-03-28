package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import io.github.tgeng.common.indexedSeqOps._
import substitutionOps._

/** First element on the left. */
type Telescope = List[Type]

/** First element on the right. */
type Context = List[Type]

extension telescopeOps on (self: Telescope) {
  def toContext = self.reverse
  def apply(s: Substitution[Term])(using Γ: Context)(using Σ: Signature) = self.substituteImpl(
    using SubstituteSpec(0, s.map(_.raise(s.size))))
    .map(_.raise(-s.size))
  def substituteImpl(using spec: SubstituteSpec[Term])(using Γ: Context)(using Σ: Signature) : Telescope = self match {
    case Nil => Nil
    case ty :: rest => reduce(ty.substituteImpl) :: rest.substituteImpl(using spec.raised)
  }
}

extension contextOps on (self: Context) {
  def toTelescope : Telescope = self.reverse
}