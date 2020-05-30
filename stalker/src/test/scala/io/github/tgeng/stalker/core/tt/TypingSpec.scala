package io.github.tgeng.stalker.core.tt

import io.github.tgeng.stalker.core.fe.builders._
import scala.language.implicitConversions
import io.github.tgeng.stalker.core.testing.CoreSpec

class TypingSpec extends CoreSpec {

  "basic term typing" in {
    given Context = Context.empty
    t"Level" ∷ t"Type 0lv"
    t"Type 0lv" ∷ t"Type 1lv"
    t"Type 6lv" ∷ t"Type 7lv"
    t"Level -> Level" ∷ t"Type 0lv"
    t"Id 0lv Level 0lv 0lv" ∷ t"Type 0lv"
    t"Refl{}" ∷ t"Id 0lv Level 0lv 0lv"
  }

  "more complex terms" in {
    // given Context = Context.empty + b"A : Type 0lv"
  }
}