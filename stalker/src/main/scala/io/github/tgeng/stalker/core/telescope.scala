package io.github.tgeng.stalker.core

case class Binding[+T](ty: T)(val name: String)

extension stringBindingOps on [T](self: String) {
  def ∷ (t: T) = Binding(t)(self)
}

extension bindingOps on [T, R](self: Binding[T]) {
  def map(f: T => R) = Binding[R](f(self.ty))(self.name)
}

/** First element on the left. */
type Telescope = List[Binding[Type]]

extension telescopeOps on (self: Telescope) {
  def apply(s: Substitution[Term])(using Γ: Context)(using Σ: Signature) = self.substituteImpl(using SubstituteSpec(0, s)) 

  def substituteImpl(using spec: SubstituteSpec[Term])(using Γ: Context)(using Σ: Signature) : List[Binding[Term]] = self match {
    case Nil => Nil
    case ty :: rest => ty.map(_.substituteImpl) :: rest.substituteImpl(using spec.raised)
  }
}
