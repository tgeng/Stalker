package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.testing.CoreSpec
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}

class ReductionSpec extends CoreSpec {

  "simple level arithmetics" in {
    t"lsuc 0lv" ~> ft"1lv"
    t"lsuc (lsuc 0lv)" ~> ft"2lv"
    t"lmax 5lv 6lv" ~> ft"6lv"
    t"lmax (lsuc 5lv) 4lv" ~> ft"6lv"
    t"lsuc (lmax (lsuc 5lv) 4lv)" ~> ft"7lv"
  }

  "level arithmetics with variables" in {
    withBindings(
      b"l : Level",
      b"m : Level",
      b"n : Level",
    ) {
      t"lsuc m" ~> ft"lsuc m"
      t"lmax m n" ~> ft"lmax m n"
      t"lsuc (lmax m n)" ~> ft"lmax (lsuc m) (lsuc n)"
      t"lsuc (lmax m 2lv)" ~> ft"lmax (lsuc m) 3lv"
      t"lsuc (lmax m (lmax n 2lv))" ~> ft"lmax (lsuc n) (lmax (lsuc m) 3lv)"
      t"lsuc (lmax m (lmax (lmax 5lv n) 2lv))" ~> ft"lmax (lsuc n) (lmax (lsuc m) 6lv)"
      t"lmax 5lv (lmax 1lv (lmax 8lv (lmax 3lv (lmax m n))))" ~> ft"lmax n (lmax m 8lv)"
      t"lmax (lmax m n) m" ~> ft"lmax m n"
      t"lmax m m" ~> ft"m"
      t"lmax (lsuc m) m" ~> ft"lsuc m"
      t"lmax (lmax (lsuc m) n) m" ~> ft"lmax (lsuc m) n"
      t"lmax (lmax (lsuc (lsuc m)) (lmax n (lsuc n))) m" ~> ft"lmax (lsuc (lsuc m)) (lsuc n)"
    }
  }

  "type arithmetics" in {
    t"Type (lsuc 0lv)" ~> ft"Type (lsuc 0lv)"
    // Whnf should not reduce under the current head
    t"Type (lsuc 0lv)" !~> ft"Type 1lv "
  }
}