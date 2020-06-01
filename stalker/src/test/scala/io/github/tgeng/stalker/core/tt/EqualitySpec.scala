package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.testing.CoreSpec

class EqualitySpec extends CoreSpec {

  "basic term equality" in {
    t"0lv" ≡ t"0lv" ∷ t"Level"
    t"0lv" ≢ t"1lv" ∷ t"Level"
    t"Level" ≡ t"Level" ∷ t"Type 0lv"
    t"Type 0lv" ≡ t"Type 0lv" ∷ t"Type 1lv"
    t"Refl{}" ≡ t"Refl{}" ∷ t"Id 0lv Level 0lv 0lv"
    t"Level -> Level" ≡ t"Level -> Level" ∷ t"Type 0lv"
  }

  "level equality" in {
    withBindings(
      b"l : Level",
      b"m : Level",
      b"n : Level",
    ) {
      t"lsuc m" ≡ t"lsuc m" ∷ t"Level"
      t"lmax m n" ≡ t"lmax m n" ∷ t"Level"
      t"lsuc (lmax m n)" ≡ t"lmax (lsuc m) (lsuc n)" ∷ t"Level"
      t"lsuc (lmax m 2lv)" ≡ t"lmax (lsuc m) 3lv" ∷ t"Level"
      t"lsuc (lmax m (lmax n 2lv))" ≡ t"lmax (lsuc n) (lmax (lsuc m) 3lv)" ∷ t"Level"
      t"lsuc (lmax m (lmax (lmax 5lv n) 2lv))" ≡ t"lmax (lsuc n) (lmax (lsuc m) 6lv)" ∷ t"Level"
      t"lmax 5lv (lmax 1lv (lmax 8lv (lmax 3lv (lmax m n))))" ≡ t"lmax n (lmax m 8lv)" ∷ t"Level"
      t"lmax (lmax m n) m" ≡ t"lmax m n" ∷ t"Level"
      t"lmax m m" ≡ t"m" ∷ t"Level"
      t"lmax (lsuc m) m" ≡ t"lsuc m" ∷ t"Level"
      t"lmax (lmax (lsuc m) n) m" ≡ t"lmax (lsuc m) n" ∷ t"Level"
      t"lmax (lmax (lsuc (lsuc m)) (lmax n (lsuc n))) m" ≡ t"lmax (lsuc (lsuc m)) (lsuc n)" ∷ t"Level"

      t"Type (lmax 1lv 2lv)" ≡ t"Type 2lv" ∷ t"Type 3lv"
      t"Type (lsuc (lmax m n))" ≡ t"Type (lmax (lsuc m) (lsuc n))" ∷ t"Type (lsuc (lsuc (lmax m n)))"
    }
  }

  "more complex terms" in {

  }
}