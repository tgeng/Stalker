package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.testing.CoreSpec
import io.github.tgeng.stalker.core.fe._
import builders._
import FDeclaration._

class SignatureSpec extends CoreSpec {

  "simple data schema" in {
    Σ +=! FData("Nat", Nil, ft"Type 0lv", Seq(FConstructor("Zero", Nil), FConstructor("Suc", List(FBinding("", ft"Nat")))))
    t"Nat" ∷ t"Type 0lv"
    ns.merge(ns.get("Nat").rightVal)
    t"Zero" ∷ t"Nat"
    t"Suc Zero" ∷ t"Nat"
  }
}