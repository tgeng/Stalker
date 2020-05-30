package io.github.tgeng.stalker.core.tt

import io.github.tgeng.stalker.core.fe.parser._
import scala.language.implicitConversions
import io.github.tgeng.stalker.core.testing.CoreSpec

class TypingSpec extends CoreSpec {

  given Context = Context.empty

  "basic term typing" in {
    t"Level" ∷ t"Type 0lv"
    t"Type 0lv" ∷ t"Type 1lv"
  }
}