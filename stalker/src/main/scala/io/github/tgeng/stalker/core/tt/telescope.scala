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

extension telescopeOps on (self: Telescope) {
  def subst(s: Substitution[Term]) : List[Binding[Term]] = self.substituteImpl(using SubstituteSpec(0, s))
  def substHead(t: Term)(using ctx: Context) : List[Binding[Term]] = self.substituteImpl(using SubstituteSpec(0, Substitution(ctx.size, ctx.size + 1, IndexedSeq(t))))
  def substHead(ts: Seq[Term])(using ctx: Context) : List[Binding[Term]] = self.substituteImpl(using SubstituteSpec(0, Substitution(ctx.size, ctx.size + ts.size, ts.toIndexedSeq.reverse)))

  def substituteImpl(using spec: SubstituteSpec[Term]) : List[Binding[Term]] = self match {
    case Nil => Nil
    case ty :: rest => ty.map(_.substituteImpl) :: rest.substituteImpl(using spec.raised)
  }

  def vars : Seq[Term] = (self.size - 1 to 0 by -1).map(i => Term.TWhnf(Whnf.WVar(i, Nil)))
}

def withCtx[T](ctx: Context)(action: (ctx: Context) ?=> T) : T = action(using ctx)
def withCtxExtendedBy[T](tele: Telescope)(action: (ctx: Context) ?=> T)(using ctx: Context) : T = action(using ctx + tele)
def withCtxExtendedBy[T](binding: Binding[Type])(action: (ctx: Context) ?=> T)(using ctx: Context) : T = action(using ctx + binding)