package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.testing.CoreSpec
import io.github.tgeng.stalker.core.fe._
import builders._
import FDeclaration._

class SignatureSpec extends CoreSpec {

  "simple data schema" in {
    Σ +=! FDataDecl("Nat", Nil, ft"Type 0lv")
    t"Nat" ∷ t"Type 0lv"
    Σ += FDataDef("Nat", Seq(FConstructor("Zero", Nil), FConstructor("Suc", List(FBinding("", ft"Nat")))))
    ns.merge(ns.get("Nat").rightVal)
    t"Zero" ∷ t"Nat"
    t"Suc Zero" ∷ t"Nat"
  }
}