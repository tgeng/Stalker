package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import scala.math.max
import io.github.tgeng.common._
import io.github.tgeng.common.sugar.{given _}
import Term._
import Whnf._
import Elimination._
import reduction.{_, given _}

def (tm: Type) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = tm match {
  case WUniverse(l) => l + 1
  case WFunction(argTy, bodyTy) => for {
    argTyL <- argTy.inferLevel
    bodyTyL <- bodyTy.inferLevel(using argTy :: Γ)
  } yield max(argTyL, bodyTyL)
  case wData@WData(qn, u) => for {
    data <- Σ(wData)
    _ <- u hasTypes data.paramTys
  } yield data.level
  case wRecord@WRecord(qn, u) => for {
    record <- Σ(wRecord)
    _ <- u hasTypes record.paramsTy
  } yield record.level
  case WId(ty, left, right) => for {
    tyL <- ty.inferLevel
    _ <- left hasType ty
    _ <- right hasType ty
  } yield tyL
  case _ => typingError(s"$tm is not a type.")
}

def (Δ: Telescope) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = Δ match {
  case Nil => 0
  case x :: rest => for {
    l1 <- x.inferLevel
    l2 <- rest.inferLevel
  } yield max(l1, l2)
}

def (tm: Term) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = ty.inferLevel match {
    case Left(e) => Left(e)
    case _ => tm ∷ ty match {
      case _ ∷ WUniverse(l) => tm.inferLevel match {
        case Right(inferredL) if inferredL == l => ()
        case Right(inferredL) => typingError(s"Universe level mismatch. Expected level $l, but got $inferredL.")
        case Left(e) => Left(e)
    }
  }
}

def (tms: List[Term]) hasTypes (Δ: Telescope)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (head: Term ∷ Type) gives (elimAndType: List[Elimination] ∷ Telescope)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (eq: Term ≡ Term) hasType (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (eqs: List[Term] ≡ List[Term]) hasTypes (ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

def (head: Term ∷ Type) givesEquality (elimEq: List[Elimination] ≡ List[Elimination] ∷ Type)(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
  TODO()
}

// ------- magic splitter -------

extension signatureOps on (self: Signature) {
  def apply(data : WData) : Result[Declaration.Data[Status.Checked, IndexedSeq]] = self(data.qn) match {
    case d : Declaration.Data[Status.Checked, IndexedSeq] => d
    case _ => typingError(s"No data schema found for ${data.qn}")
  }

  def apply(record : WRecord) : Result[Declaration.Record[Status.Checked, IndexedSeq]] = self(record.qn) match {
    case r : Declaration.Record[Status.Checked, IndexedSeq] => r
    case _ => typingError(s"No record schema found for ${record.qn}")
  }

  def apply(redux : TRedux) : Result[Declaration.Definition[Status.Checked, IndexedSeq]] = self(redux.fn) match {
    case d : Declaration.Definition[Status.Checked, IndexedSeq] => d
    case _ => typingError(s"No record schema found for ${redux.fn}")
  }
}

type Result = Either[TypingError, *]
type Level = Int

case class ∷[X, Y](x: X, y: Y)

case class ≡[X, Y](x: X, y: Y)

extension termTyping on (tm: Term) {
  def ∷ (ty: Type) = new ∷(tm, ty)
}

extension termsTyping on (tms: List[Term]) {
  def ∷ (tys: Telescope) = new ∷(tms, tys)
}

extension isEqual on [X](lhs: X) {
  def ≡ (rhs: X) = new ≡(lhs, rhs)
}

case class TypingError(msg: String)

def typingError(msg: String) : Either[TypingError, Nothing] = Left(TypingError(msg))
