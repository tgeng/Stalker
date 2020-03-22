package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import io.github.tgeng.common._
import io.github.tgeng.common.sugar.{given _}
import Whnf._
import Elimination._
import reduction.{_, given _}

def (tm: Whnf) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Option[Level]] = {
  ty match {
    case WUniverse(l) => tm hasType WUniverseX match {
      case Right(Some(inferredL)) if inferredL == l => None
      case Right(Some(inferredL)) => typingError(s"Universe level mismatch. Expected level $l, but got $inferredL.")
      case _ => throw AssertionError("Check against type WUniverseX must yield either a level or an error.")
    }
    case WUniverseX => tm match {
      case WUniverse(l) => l + 1
      case WFunction(argTy, bodyTy) => TODO()
    }
  }
}

def (tms: List[Whnf]) hasTypes (Δ: Telescope)(using Γ: Context)(using Σ: Signature) : Result[Option[Level]] = {
  TODO()
}

def (head: Whnf ∷ Type) gives (elimAndType: List[Elimination] ∷ Telescope)(using Γ: Context)(using Σ: Signature) : Result[Option[Level]] = {
  TODO()
}

def (eq: Whnf ≡ Whnf) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Option[Level]] = {
  TODO()
}

def (eqs: List[Whnf] ≡ List[Whnf]) hasTypes (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Option[Level]] = {
  TODO()
}

def (head: Whnf ∷ Type) givesEquality (elimEq: List[Elimination] ≡ List[Elimination] ∷ Type)(using Γ: Context)(using Σ: Signature) : Result[Option[Level]] = {
  TODO()
}

// ------- magic splitter -------

type Result = Either[TypingError, *]
type Level = Int
type Type = Whnf

case class ∷[X, Y](x: X, y: Y)

case class ≡[X, Y](x: X, y: Y)

extension hasType on [X](ty: Whnf) {
  def ∷ (x: X) = new ∷(x, ty)
}

extension hasTypes on [X](Δ: Telescope) {
  def ∷ (x: X) = new ∷(x, Δ)
}

extension isEqual on [X](lhs: X) {
  def ≡ (rhs: X) = new ≡(lhs, rhs)
}

case class TypingError(msg: String)

def typingError(msg: String) : Either[TypingError, Nothing] = Left(TypingError(msg))
