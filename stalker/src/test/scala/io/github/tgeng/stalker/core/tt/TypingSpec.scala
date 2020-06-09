package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.testing.CoreSpec

class TypingSpec extends CoreSpec {

  "basic term typing" in {
    t"Level" ∷ t"Type 0lv"
    t"Type 0lv" ∷ t"Type 1lv"
    t"Type 6lv" ∷ t"Type 7lv"
    t"Level -> Level" ∷ t"Type 0lv"
    t"Id 0lv Level 0lv 0lv" ∷ t"Type 0lv"
    t"Refl{}" ∷ t"Id 0lv Level 0lv 0lv"
  }

  "simple function applications" in {
    withBindings(
      b"X : Type 0lv",
      b"Y : Type 0lv",
      b"Z : Type 0lv",
      b"x : X",
      b"y : Y",
      b"fn : X -> Y -> Z",
    ) {
      t"fn x" ∷ t"Y -> Z"
      t"fn x y" ∷ t"Z"
    }
  }

  "dependent function applications" in {
    withBindings(
      b"X : Type 0lv",
      b"Y : X -> Type 0lv",
      b"Z : (x : X) -> Y x -> Type 0lv",
      b"x : X",
      b"y : Y x",
      b"z : Z x y",
      b"fn : (x : X) -> (y : Y x) -> Z x y",
    ) {
      t"fn x" ∷ t"(y : Y x) -> Z x y"
      t"fn x y" ∷ t"Z x y"
    }
  }

  "type hierarchy" in {
    withBindings(
      b"m : Level",
      b"n : Level",
    ) {
      t"Type m" ∷ t"Type (lsuc m)"
      t"Type (lmax m n)" ∷ t"Type (lsuc (lmax m n))"
      t"Type (lmax 0lv (lmax m 2lv))" ∷ t"Type (lmax (lsuc m) (lsuc 2lv))"
      t"Type (lmax 0lv (lsuc (lmax 3lv n)))" ∷ t"Type (lmax (lsuc (lsuc n)) 5lv)"
    }
  }

  "Id type" in {
    withBindings(
      b"X : Type 1lv",
      b"x : X",
      b"y : X",
    ) {
      t"Refl{}" ∷ t"Id 1lv X x x"
      t"Refl{}" !∷ t"Id 1lv X x y"
    }
  }

  "with data schema" - {

    Σ +=! decl"""
    |data Nat : Type 0lv where
    |  Zero : Nat
    |  Suc : Nat -> Nat
    """

    Σ +=! decl"""
    |data Vector (n : Nat)(A : Type 0lv) : Type 0lv where
    |  Nil : Id 0lv Nat n Nat.Zero -> Vector n A
    |  Cons : (m : Nat) -> A -> Vector m A -> Id 0lv Nat (Nat.Suc m) n -> Vector n A
    """

    "simple data type" in {
      t"Nat" ∷ t"Type 0lv"
      t"Nat.Zero" ∷ t"Nat"
      t"Nat.Suc Nat.Zero" ∷ t"Nat"

      t"Vector Nat.Zero Level" ∷ t"Type 0lv"
      t"Vector.Nil Refl" ∷ t"Vector Nat.Zero Level"
      t"Vector.Cons Nat.Zero 1lv (Vector.Nil Refl) Refl" ∷ t"Vector (Nat.Suc Nat.Zero) Level"
      t"Vector.Cons Nat.Zero 1lv (Vector.Nil Refl) Refl" !∷ t"Vector Nat.Zero Level"
    }
  }
}