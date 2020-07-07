package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.common.eitherOps
import io.github.tgeng.stalker
import stalker.core.testing._
import stalker.core.fe.builders._

import debug._

class StdlibSpec extends CoreSpec {
  "nat" in {
    withSignature("stalker.data.nat.base") {
      t"Nat" ∷ t"Type 0lv"
      t"0" ∷ t"Nat"
      t"1" ∷ t"Nat"
      t"5" ∷ t"Nat"
      t"+ 3 4" ≡ t"7" ∷ t"Nat"
    }
    withSignature("stalker.data.nat.base") {
      t"Nat" ∷ t"Type 0lv"
    }
  }
  "vector" in {
    withSignature("stalker.data.vector.base") {
      t"Vector 0lv 3 Nat" ∷ t"Type 0lv"
    }
  }
}