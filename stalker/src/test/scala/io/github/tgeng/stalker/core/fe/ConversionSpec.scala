package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.testing.CoreSpec
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.tt.stringBindingOps
import io.github.tgeng.stalker.core.common.LeafNamespace

import Term._
import Whnf._
import Elimination._

class ConversionSpec extends CoreSpec {

  "FTerm -> Term" - {
    "basic terms" in {
      assert(fterm("Type").tt == TRedux("stalker.builtins.Type", Nil))
      assert(fterm("5lv").tt == TWhnf(WLevel(5, Set.empty)))
      assert(fterm("con{}").tt == TWhnf(WCon("con", Nil)))
      assert(fterm("(A : Type) -> Type").tt == TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", Nil), TRedux("stalker.builtins.Type", Nil))))
      assert(fterm("(A : Type) -> A").tt == TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", Nil), TWhnf(WVar(0, Nil)))))
    }

    "more complex terms" in {
      namespace("Vector") = LeafNamespace("stalker.collection.Vector")
      namespace("Nat") = LeafNamespace("stalker.util.Nat")
      namespace("String") = LeafNamespace("stalker.util.String")
      namespace("Integer") = LeafNamespace("stalker.util.Integer")
      assert(fterm("(n : Nat) -> (A : Type 0lv) -> Vector n A").tt == 
        TWhnf(WFunction(
          "n" ∷ TRedux("stalker.util.Nat", List()),
          TWhnf(WFunction(
            "A" ∷ TRedux("stalker.builtins.Type", List(ETerm(TWhnf(WLevel(0,Set()))))),
            TRedux("stalker.collection.Vector", List(ETerm(TWhnf(WVar(1,List()))), ETerm(TWhnf(WVar(0,List()))))))))))
      assert(fterm("con{Nat, String, Integer}").tt == 
        TWhnf(WCon("con",List(
          TRedux("stalker.util.Nat", List()), 
          TRedux("stalker.util.String", List()), 
          TRedux("stalker.util.Integer", List())))))
      assert(fterm("con{Nat -> Nat, String -> String, (n : Nat) -> (A : Type 0lv) -> Vector n A}").tt == 
        TWhnf(WCon("con", List(
          TWhnf(WFunction("" ∷ TRedux("stalker.util.Nat", List()), TRedux("stalker.util.Nat", List()))),
          TWhnf(WFunction("" ∷ TRedux("stalker.util.String", List()), TRedux("stalker.util.String", List()))),
          TWhnf(WFunction("n" ∷ TRedux("stalker.util.Nat", List()),
            TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", List(ETerm(TWhnf(WLevel(0, Set()))))),
              TRedux("stalker.collection.Vector", List(ETerm(TWhnf(WVar(1, List()))), ETerm(TWhnf(WVar(0, List())))))))))))))
    }
  }
}