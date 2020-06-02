package io.github.tgeng.stalker.core.tt

import io.github.tgeng.common.extraIntOps

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
  def pvars : Seq[Pattern] = {
    val size = self.size
    self.zipWithIndex.map((b, i) => Pattern.PVar(size - 1 - i)(b.name))
  }
}

def withCtx[T](ctx: Context)(action: (ctx: Context) ?=> T) : T = action(using ctx)
def withCtxExtendedBy[T](telescope: Telescope)(action: (ctx: Context) ?=> T)(using ctx: Context) : T = action(using ctx + telescope)
def withCtxExtendedBy[T](binding: Binding[Type])(action: (ctx: Context) ?=> T)(using ctx: Context) : T = action(using ctx + binding)