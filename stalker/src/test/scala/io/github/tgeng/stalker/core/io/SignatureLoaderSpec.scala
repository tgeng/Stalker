package io.github.tgeng.stalker.core.io

import scala.language.implicitConversions
import io.github.tgeng.stalker
import stalker.core.testing._
import stalker.core.fe.builders._

class SignatureLoaderSpec extends CoreSpec {
  withSignature("io.github.tgeng.stalker.core.io.basic") {
    "basic typing" in {
      t"unit" ∷ t"Unit"
      t"MyLevel" ∷ t"Type 0lv"
      t"myLmax 1lv 2lv" ~> ft"2lv"
      t"Pair{0lv 1lv}" ∷ t"Pair 0lv Level"
    }
  }
}