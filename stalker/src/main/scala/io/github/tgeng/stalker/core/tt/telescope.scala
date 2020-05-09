package io.github.tgeng.stalker.core.tt

case class Binding[+T](ty: T)(val name: String)

extension stringBindingOps on [T](self: String) {
  def ∷ (t: T) = Binding(t)(self)
}

extension bindingOps on [T, R](self: Binding[T]) {
  def map(f: T => R) = Binding[R](f(self.ty))(self.name)
}

/** First element on the left. */
type Telescope = List[Binding[Type]]

given Substitutable[Telescope, Term, List[Binding[Term]]] {
  def (ts: Telescope) substituteImpl(using spec: SubstituteSpec[Term]) : List[Binding[Term]] = ts match {
    case Nil => Nil
    case ty :: rest => ty.map(_.substituteImpl) :: rest.substituteImpl(using spec.raised)
  }
}

extension telescopeOps on (self: Telescope) {
  def vars : Seq[Term] = (self.size - 1 to 0 by -1).map(i => Term.TWhnf(Whnf.WVar(i, Nil)))
  def pvars : Seq[Pattern] = (self.size - 1 to 0 by -1).map(Pattern.PVar(_))
}

def withCtx[T](ctx: Context)(action: (ctx: Context) ?=> T) : T = action(using ctx)
def withCtxExtendedBy[T](tele: Telescope)(action: (ctx: Context) ?=> T)(using ctx: Context) : T = action(using ctx + tele)
def withCtxExtendedBy[T](binding: Binding[Type])(action: (ctx: Context) ?=> T)(using ctx: Context) : T = action(using ctx + binding)