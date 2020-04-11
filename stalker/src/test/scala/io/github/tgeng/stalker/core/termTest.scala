package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import io.github.tgeng.stalker.testing.UnitSpec

import io.github.tgeng.stalker.core._
import io.github.tgeng.stalker.core.Term._
import io.github.tgeng.stalker.core.Whnf._

class TermSpec extends UnitSpec {
  "empty Σ and Γ" - {
    given Σ : Signature = signatureBuilder.Signature.create
    given Γ : Context = Context.empty

    "type level" in {
      TWhnf(WUniverse(0)) should haveLevel(1)
    }

    "term typing" in {
      TWhnf(WUniverse(0)) should haveType(TWhnf(WUniverse(1)))
    }
  }
}