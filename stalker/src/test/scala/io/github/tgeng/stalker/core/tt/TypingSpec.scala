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
}