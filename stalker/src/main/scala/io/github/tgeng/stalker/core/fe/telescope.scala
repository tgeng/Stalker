package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Binding => DbBinding, Term => DbTerm}

case class Binding(name: String, ty: Term) {
  def toDbBinding(using ctx: NameContext) : Result[DbBinding[DbTerm]] = for {
    dbTerm <- ty.toDbTerm
  } yield DbBinding(dbTerm)(name)
}

type Telescope = List[Binding]

extension telescopeOps on (self: Telescope) {
  def toDbTelescope(using ctx: NameContext) : Result[List[DbBinding[DbTerm]]] =
    self.liftMap(_.toDbBinding)
}