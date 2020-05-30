package io.github.tgeng.stalker.core.tt

import io.github.tgeng.stalker.core.fe.parser._
import scala.language.implicitConversions
import io.github.tgeng.stalker.core.testing.CoreSpec

class TypingSpec extends CoreSpec {

  "basic term typing" in {
    given Context = Context.empty
    t"Level" should haveType(t"Type 0lv")
    t"Type 0lv" should haveType(t"Type 1lv")
  }
}