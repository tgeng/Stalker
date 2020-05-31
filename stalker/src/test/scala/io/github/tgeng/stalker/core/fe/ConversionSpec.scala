package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.testing.CoreSpec
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.fe.parser._
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.tt.stringBindingOps
import io.github.tgeng.stalker.core.common.LeafNamespace

import Term._
import Whnf._
import Elimination._

class ConversionSpec extends CoreSpec {

  ns("Vector") = LeafNamespace("stalker.collection.Vector")
  ns("Nat") = LeafNamespace("stalker.util.Nat")
  ns("String") = LeafNamespace("stalker.util.String")
  ns("Integer") = LeafNamespace("stalker.util.Integer")

  "FTerm -> Term" - {
    "basic terms" in {
      assert(ft"Type".tt == TRedux("stalker.builtins.Type", Nil))
      assert(ft"5lv".tt == TWhnf(WLConst(5)))
      assert(ft"con{}".tt == TWhnf(WCon("con", Nil)))
      assert(ft"(A : Type) -> Type".tt == TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", Nil), TRedux("stalker.builtins.Type", Nil))))
      assert(ft"(A : Type) -> A".tt == TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", Nil), TWhnf(WVar(0, Nil)))))
    }

    "more complex terms" in {
      assert(ft"(n : Nat) -> (A : Type 0lv) -> Vector n A".tt == 
        TWhnf(WFunction(
          "n" ∷ TRedux("stalker.util.Nat", List()),
          TWhnf(WFunction(
            "A" ∷ TRedux("stalker.builtins.Type", List(ETerm(TWhnf(WLConst(0))))),
            TRedux("stalker.collection.Vector", List(ETerm(TWhnf(WVar(1,List()))), ETerm(TWhnf(WVar(0,List()))))))))))
      assert(ft"con{Nat, String, Integer}".tt == 
        TWhnf(WCon("con",List(
          TRedux("stalker.util.Nat", List()), 
          TRedux("stalker.util.String", List()), 
          TRedux("stalker.util.Integer", List())))))
      assert(ft"con{Nat -> Nat, String -> String, (n : Nat) -> (A : Type 0lv) -> Vector n A}".tt == 
        TWhnf(WCon("con", List(
          TWhnf(WFunction("" ∷ TRedux("stalker.util.Nat", List()), TRedux("stalker.util.Nat", List()))),
          TWhnf(WFunction("" ∷ TRedux("stalker.util.String", List()), TRedux("stalker.util.String", List()))),
          TWhnf(WFunction("n" ∷ TRedux("stalker.util.Nat", List()),
            TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", List(ETerm(TWhnf(WLConst(0))))),
              TRedux("stalker.collection.Vector", List(ETerm(TWhnf(WVar(1, List()))), ETerm(TWhnf(WVar(0, List())))))))))))))
    }
  }

  "Term -> FTerm" - {
    "basic terms" in {
      assert(TRedux("stalker.builtins.Type", Nil).fe == ft"Type")
      assert(TWhnf(WFunction("" ∷ TRedux("stalker.builtins.Type", Nil), TRedux("stalker.builtins.Type", Nil))).fe == ft"Type -> Type")
      assert(TWhnf(WLConst(5)).fe == ft"5lv")
      assert(TWhnf(WType(TWhnf(WLConst(5)))).fe == ft"Type 5lv")
      assert(TWhnf(WLevelType).fe == ft"Level")
      assert(TWhnf(WData("a.b.c", Nil)).fe == ft"a.b.c")
      assert(TWhnf(WRecord("a.b.c", Nil)).fe == ft"a.b.c")
      assert(TWhnf(WId(TWhnf(WLConst(0)), TWhnf(WData("a.b.c", Nil)), TWhnf(WCon("con1", Nil)), TWhnf(WCon("con2", Nil)))).fe == ft"Id 0lv a.b.c con1{} con2{}")
      assert(TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", Nil), TWhnf(WVar(0, Nil)))).fe == ft"(A : Type) -> A")

      assert(TWhnf(WFunction(
          "n" ∷ TRedux("stalker.util.Nat", List()),
          TWhnf(WFunction(
            "A" ∷ TRedux("stalker.builtins.Type", List(ETerm(TWhnf(WLConst(0))))),
            TRedux("stalker.collection.Vector", List(ETerm(TWhnf(WVar(1,List()))), ETerm(TWhnf(WVar(0,List()))))))))).fe ==
        ft"(n : Nat) -> (A : Type 0lv) -> Vector n A")

      assert(TWhnf(WCon("con",List(
          TRedux("stalker.util.Nat", List()), 
          TRedux("stalker.util.String", List()), 
          TRedux("stalker.util.Integer", List())))).fe ==
        ft"con{Nat, String, Integer}")
      assert(TWhnf(WCon("con", List(
          TWhnf(WFunction("" ∷ TRedux("stalker.util.Nat", List()), TRedux("stalker.util.Nat", List()))),
          TWhnf(WFunction("" ∷ TRedux("stalker.util.String", List()), TRedux("stalker.util.String", List()))),
          TWhnf(WFunction("n" ∷ TRedux("stalker.util.Nat", List()),
            TWhnf(WFunction("A" ∷ TRedux("stalker.builtins.Type", List(ETerm(TWhnf(WLConst(0))))),
              TRedux("stalker.collection.Vector", List(ETerm(TWhnf(WVar(1, List()))), ETerm(TWhnf(WVar(0, List())))))))))))).fe ==
        ft"con{Nat -> Nat, String -> String, (n : Nat) -> (A : Type 0lv) -> Vector n A}")
    }
  }

  "FTerm <-> Term" - {
    "more more more!" in {
      roundtrip(
        """
        (vecFn : (n : Nat) -> (A : Type) -> Vector n A) ->
        (m : Nat) ->
        (n : Nat) ->
        Vector n (Vector m String)
        """,
        """
        (veryLongFn : (a : Nat) ->
                      (b : Integer) ->
                      (c : Nat -> Integer -> String) ->
                      (d : (n : Nat) -> Integer -> Vector n String) ->
                      Type) ->
        (a : Nat) ->
        (b : Integer) ->
        (c : Nat -> Integer -> String) ->
        (d : (n : Nat) -> Integer -> Vector n String) ->
        veryLongFn a b c d con1{a, b, c, d}
        """,
        "(m : Nat) -> (f1 : Nat -> Nat) -> (f2 : Nat -> Type) -> f2 (f1 m) (f1 (f1 m))",
      )
    }
  }

  private def roundtrip(terms: String*) = {
    for (t <- terms) {
      val fterm = ft(t)
      assert(fterm.tt.fe == fterm)
    }
  }
}