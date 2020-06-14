package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.testing.CoreSpec

class ElaborationSpec extends CoreSpec {

    Σ +=! decl"""
    |data Nat : Type 0lv where
    |  Zero : Nat
    |  Suc : Nat -> Nat
    """

    Σ +=! decl"""
    |def plus : Nat -> Nat -> Nat
    |  m Nat.Zero = m
    |  m (Nat.Suc n) = Nat.Suc (plus m n)
    """

    Σ +=! decl"""
    |def suc : Nat -> Nat
    |  n = Nat.Suc n
    """

    Σ +=! decl"""
    |def _0 : Nat
    |  = Nat.Zero
    """

    Σ +=! decl"""
    |def _1 : Nat
    |  = suc _0
    """

    Σ +=! decl"""
    |def _2 : Nat
    |  = suc _1
    """

    Σ +=! decl"""
    |def _3 : Nat
    |  = suc _2
    """

    Σ +=! decl"""
    |def _4 : Nat
    |  = suc _3
    """

    "plus" in {
      t"plus _1 _1" ≡ t"_2" ∷ t"Nat"
      t"plus _2 _2" ≡ t"_4" ∷ t"Nat"
    }
}