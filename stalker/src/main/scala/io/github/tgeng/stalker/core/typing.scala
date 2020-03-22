package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import scala.math.max
import io.github.tgeng.common._
import io.github.tgeng.common.sugar.{given _}
import Whnf._
import Elimination._
import reduction.{_, given _}

def (tm: Whnf) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = tm match {
  case WUniverse(l) => l + 1
  case WFunction(argTy, bodyTy) => for {
    argTyL <- argTy.inferLevel
  } yield argTyL
}

def (Δ: Telescope) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = Δ match {
  case Nil => 0
  case x :: rest => for {
    l1 <- x.inferLevel
    l2 <- rest.inferLevel
  } yield max(l1, l2)
}

def (eq: Type ≡ Type) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = TODO()

def (tm: Whnf) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  ty match {
    case WUniverse(l) => tm.inferLevel match {
      case Right(inferredL) if inferredL == l => ()
      case Right(inferredL) => typingError(s"Universe level mismatch. Expected level $l, but got $inferredL.")
      case Left(e) => Left(e)
    }
  }
}

def (tms: List[Whnf]) hasTypes (Δ: Telescope)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (head: Whnf ∷ Type) gives (elimAndType: List[Elimination] ∷ Telescope)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (eq: Whnf ≡ Whnf) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (eqs: List[Whnf] ≡ List[Whnf]) hasTypes (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (head: Whnf ∷ Type) givesEquality (elimEq: List[Elimination] ≡ List[Elimination] ∷ Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
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
