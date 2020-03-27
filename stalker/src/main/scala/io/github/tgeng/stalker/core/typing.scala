package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import scala.math.max
import io.github.tgeng.common._
import io.github.tgeng.common.sugar.{given _}
import Term._
import Whnf._
import Elimination._
import reduction.{_, given _}
import substitutionConversion.{given _}

def (tm: Type) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = tm match {
  case WUniverse(l) => l + 1
  case WFunction(argTy, bodyTy) => for {
    argTyL <- argTy.inferLevel
    bodyTyL <- bodyTy.inferLevel(using argTy :: Γ)
  } yield max(argTyL, bodyTyL)
  case wData@WData(qn, u) => for {
    data <- Σ(wData)
    _ <- u ∷ data.paramTys
  } yield data.level
  case wRecord@WRecord(qn, u) => for {
    record <- Σ(wRecord)
    _ <- u ∷ record.paramsTy
  } yield record.level
  case WId(ty, left, right) => for {
    tyL <- ty.inferLevel
    _ <- left ∷ ty
    _ <- right ∷ ty
  } yield tyL
  case _ => typingError(s"$tm is not a type.")
}

def (Δ: Telescope) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = Δ match {
  case Nil => 0
  case x :: rest => for {
    l1 <- x.inferLevel
    l2 <- rest.inferLevel(using x :: Γ)
  } yield max(l1, l2)
}

def (eq: ≡[Type]) inferLevel (using Γ: Context)(using Σ: Signature) : Result[Level] = TODO()

object typing { given key as typing.type = this }
def (j: Term ∷ Type) apply (using Γ: Context)(using Σ: Signature)(using d : typing.type) : Result[Unit] = j match {
  // Types
  case _A ∷ WUniverse(l) => _A.inferLevel match {
    case Right(inferredL) if inferredL == l => ()
    case Right(inferredL) => judgementError(j)
    case Left(e) => Left(e)
  }
  // Heads
  case TWhnf(WVar(idx, elims)) ∷ _A => for {
    _ <- TWhnf(WVar(idx, Nil)) ∷ Γ(idx) |- elims ∷ _A
  } yield ()
  case (r@TRedux(fn, elims)) ∷ _A => for {
    definition <- Σ(r)
    _ <- TRedux(fn, Nil) ∷ definition.ty |- elims ∷ _A
  } yield ()
  // Values
  case TWhnf(WCon(c, v̅)) ∷ (wData@WData(d, u̅)) => for {
    data <- Σ(wData)
    constructor <- data(c)     
    _ <- u̅ ∷ data.paramTys
    _ <- v̅ ∷ constructor.argTys(v̅)
  } yield ()
  case TWhnf(WRefl) ∷ WId(_A, u, v) if (u == v) => for {
    _ <- u ∷ _A
  } yield ()
  case _ => judgementError(j)
}

object telescopeTyping { given key as telescopeTyping.type = this }
def (j: List[Term] ∷ Telescope) apply (using Γ: Context)(using Σ: Signature)(using d : telescopeTyping.type) : Result[Unit] = j match {
  case Nil ∷ Nil => ()
  case (x :: u̅) ∷ (_A :: _Δ) => for {
    _ <- x ∷ _A
    _ <- _Δ.inferLevel
    _ <- (u̅ ∷ _Δ)(using _Δ(x))
  } yield ()
  case _ => judgementError(j)
}

object drvElim { given key as drvElim.type = this }
def (j: Term ∷ Type |- List[Elimination] ∷ Type) apply (using Γ: Context)(using Σ: Signature)(using d : drvElim.type) : Result[Unit] = {
  TODO()
}

object eqTyping { given key as eqTyping.type = this }
def (j: ≡[Term] ∷ Type) apply (using Γ: Context)(using Σ: Signature)(using d : eqTyping.type) : Result[Unit] = {
  TODO()
}

object eqTelescopeTyping { given key as eqTelescopeTyping.type = this }
def (j: ≡[List[Term]] ∷ Telescope) apply (using Γ: Context)(using Σ: Signature)(using d : eqTelescopeTyping.type) : Result[Unit] = {
  TODO()
}

object drvEqElim { given key as drvEqElim.type = this }
def (j: Term ∷ Type |- ≡[List[Elimination]] ∷ Type) check(using Γ: Context)(using Σ: Signature)(using d : drvEqElim.type) : Result[Unit] = {
  TODO()
}

// ------- magic splitter -------

extension signatureTypingOps on (self: Signature) {
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

extension dataOps on (self: Declaration.Data[Status.Checked, IndexedSeq]) {
  def apply(name: String) : Result[Constructor] = self.cons.find(_.name == name) match {
    case Some(c) => c
    case None => typingError(s"Cannot find constructor '$name' for data ${self.qn}.")
  }
}

extension recordOps on (self: Declaration.Record[Status.Checked, IndexedSeq]) {
  def apply(name: String) : Result[Field] = self.fields.find(_.name == name) match {
    case Some(f) => f
    case None => typingError(s"Cannot find field '$name' for record ${self.qn}.")
  }
}

type Result = Either[TypingError, *]
type Level = Int

case class ∷[X, Y](x: X, y: Y)

case class ≡[X](a: X, b: X)

case class |-[X, Y](a: X, b: Y)

extension typingRelation on [X, Y](x: X) {
  def ∷ (y: Y) = new ∷(x, y)
}

extension equalityRelation on [X](x: X) {
  def ≡ (y: X) = new ≡(x, y)
}

extension derivationRelation on [X, Y](x: X) {
  def |- (y: Y) = new |-(x, y)
}

given typingRightConversion[A, B, C](using bToC: Conversion[B, C]) as Conversion[A ∷ B, A ∷ C] = (ab: A ∷ B) => ab match { case a ∷ b => a ∷ bToC(b)}

case class TypingError(msg: String)

def judgementError(judgement: ∷[?, ?] | |-[?, ?] | ≡[?] ) : Either[TypingError, Nothing] = typingError(s"Invalid judgement $judgement")
def typingError(msg: String) : Either[TypingError, Nothing] = Left(TypingError(msg))
