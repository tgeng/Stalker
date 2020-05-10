package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.{Binding => TtBinding, Term => TtTerm}

type Telescope = List[Binding]

extension telescopeOps on (self: Telescope) {
  def tt(using ctx: NameContext) : Result[List[TtBinding[TtTerm]]] =
    self.liftMap(_.tt)
}