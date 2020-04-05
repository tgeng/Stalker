package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import io.github.tgeng.stalker.testing.UnitSpec

import io.github.tgeng.stalker.core._
import io.github.tgeng.stalker.core.Term._
import io.github.tgeng.stalker.core.Whnf._

class TermSpec extends UnitSpec {
  "with empty signature" - {
    given Σ : Signature = mutable.Signature.create
    "with empty context" - {
      given Γ : Telescope = List.empty
      "term typing" in {
        TWhnf(WUniverse(0)) ∷ (WUniverse(1)) should check
      }
    }
  }
}