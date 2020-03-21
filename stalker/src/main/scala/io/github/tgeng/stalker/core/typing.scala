package io.github.tgeng.stalker.core

import Term._
import Whnf._
import Elimination._

def (ty: Type) level (using Γ: Context)(using Σ: Signature) : Result[Level] = {
  throw UnsupportedOperationException()
}

def (Δ: Telescope) level (using Γ: Context)(using Σ: Signature) : Result[Level] = {
  throw UnsupportedOperationException()
}

def (eq: Type ≡ Type) level (using Γ: Context)(using Σ: Signature) : Result[Level] = {
  throw UnsupportedOperationException()
}

def (tm: Term) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  throw UnsupportedOperationException()
}

def (tms: List[Term]) hasTypes (Δ: Telescope)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  throw UnsupportedOperationException()
}

def (head: Term ⫶ Type) gives (elimAndType: List[Elimination] ⫶ Telescope)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  throw UnsupportedOperationException()
}

def (eq : Term ≡ Term) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  throw UnsupportedOperationException()
}

def (eqs : List[Term] ≡ List[Term]) hasTypes (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  throw UnsupportedOperationException()
}

def (head: Term ⫶ Type) givesEquality (elimEq: List[Elimination] ≡ List[Elimination] ⫶ Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  throw UnsupportedOperationException()
}

// ------- magic splitter -------

type Level = Int
type Result = Either[TypingError, *]

type Type = Term

case class ⫶[X, Y](x: X, y: Y)
case class ≡[X, Y](x: X, y: Y)

extension hasType on [X](ty: Term) {
  def ⫶ (x: X) = new ⫶(x, ty)
}

extension hasTypes on [X](Δ: Telescope) {
  def ⫶ (x: X) = new ⫶(x, Δ)
}

extension isEqual on [X](lhs: X) {
  def ≡ (rhs: X) = new ≡(lhs, rhs)
}

case class TypingError()
