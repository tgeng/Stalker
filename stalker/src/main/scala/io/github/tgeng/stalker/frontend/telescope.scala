package io.github.tgeng.stalker.frontend

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.{Binding => DbBinding, Term => DbTerm}

case class Binding(name: String, ty: Term)

extension bindingOps on (self: Binding) {
  def toDbBinding(using ctx: NameContext) : Result[DbBinding[DbTerm]] = for {
    dbTerm <- self.ty.toDbTerm
  } yield DbBinding(dbTerm)(self.name)
}

type Telescope = List[Binding]

extension telescopeOps on (self: Telescope) {
  def toDbTelescope(using ctx: NameContext) : Result[List[DbBinding[DbTerm]]] =
    self.liftMap(_.toDbBinding)
}