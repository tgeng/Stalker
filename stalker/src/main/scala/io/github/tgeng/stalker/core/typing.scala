package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import scala.math.max
import io.github.tgeng.common._
import Term._
import Whnf._
import Elimination._
import reduction.{_, given _}
import substitutionConversion.{given _}

def inferLevel(tm: Type) (using Γ: Context)(using Σ: Signature) : Result[Level] = tm match {
  case WUniverse(l) => Right(l + 1)
  case WFunction(argTy, bodyTy) => for {
    argTyL <- inferLevel(argTy)
    bodyTyL <- inferLevel(bodyTy)(using argTy :: Γ)
  } yield max(argTyL, bodyTyL)
  case _D@WData(qn, u) => for {
    data <- Σ(_D)
    _ <- check(u ∷ data.paramTys)
  } yield data.level
  case _R@WRecord(qn, u) => for {
    record <- Σ(_R)
    _ <- check(u ∷ record.paramsTy)
  } yield record.level
  case WId(ty, left, right) => {
    val tyW = reduce(ty)
    for {
      tyL <- inferLevel(tyW)
      _ <- check(left ∷ tyW)
      _ <- check(right ∷ tyW)
    } yield tyL
  }
  case _ => typingError(s"$tm is not a type.")
}

def inferLevel(Δ: Telescope)(using Γ: Context)(using Σ: Signature) : Result[Level] = Δ match {
  case Nil => Right(0)
  case x :: rest => for {
    l1 <- inferLevel(x)
    l2 <- inferLevel(rest)(using x :: Γ)
  } yield max(l1, l2)
}

def inferLevel(eq: ≡[Type])(using Γ: Context)(using Σ: Signature) : Result[Level] = TODO()

object typing { given key as typing.type = this }
def check(j: Term ∷ Type)(using Γ: Context)(using Σ: Signature)(using d : typing.type) : Result[Unit] = j match {
  // Types
  case _A ∷ WUniverse(l) => inferLevel(_A) match {
    case Right(inferredL) if inferredL == l => Right(())
    case Right(inferredL) => judgementError(j)
    case Left(e) => Left(e)
  }
  // Heads
  case TWhnf(WVar(idx, e̅)) ∷ _A => for {
    _ <- check(TWhnf(WVar(idx, Nil)) ∷ Γ(idx) |- e̅ ∷ _A)
  } yield ()
  case (r@TRedux(fn, e̅)) ∷ _A => for {
    definition <- Σ(r)
    _ <- check(TRedux(fn, Nil) ∷ definition.ty |- e̅ ∷ _A)
  } yield ()
  // Values
  case TWhnf(WCon(c, v̅)) ∷ (wData@WData(d, u̅)) => for {
    data <- Σ(wData)
    constructor <- data(c)     
    _ <- check(u̅ ∷ data.paramTys)
    _ <- check(v̅ ∷ constructor.argTys(v̅))
  } yield ()
  case TWhnf(WRefl) ∷ WId(_A, u, v) => for {
    _ <- check(u ≡ v ∷ _A)
    _ <- check(u ∷ _A)
  } yield ()
  case _ => judgementError(j)
}

object telescopeTyping { given key as telescopeTyping.type = this }
def check(j: List[Term] ∷ Telescope)(using Γ: Context)(using Σ: Signature)(using d : telescopeTyping.type) : Result[Unit] = j match {
  case Nil ∷ Nil => Right(())
  case (x :: u̅) ∷ (_A :: _Δ) => for {
    _ <- check(x ∷ _A)
    _ <- inferLevel(_Δ)
    _ <- check(u̅ ∷ _Δ)(using _Δ(x))
  } yield ()
  case _ => judgementError(j)
}

object elimTyping { given key as elimTyping.type = this }
def check(j: Term ∷ Type |- List[Elimination] ∷ Type)(using Γ: Context)(using Σ: Signature)(using d : elimTyping.type) : Result[Unit] = j match {
  case u ∷ _A |- Nil ∷ _B  => for {
    _ <- inferLevel(_A ≡ _B)
  } yield ()
  case u ∷ WFunction(_A, _B) |- (ETerm(v) :: e̅) ∷ _C => for {
    _ <- check(v ∷ _A)
    uv <- app(u, v)
    _Bv = _B(v)
    _ <- check(uv ∷ _Bv)
    _ <- check(uv ∷ _Bv |- e̅ ∷ _C)
  } yield ()
  case u ∷ (_R@WRecord(_, v̅)) |- (EProj(π) :: e̅) ∷ _C => for {
    record <- Σ(_R)
    field <- record(π) 
    uπ <- app(u, π)
    _ <- check(uπ ∷ field.ty(v̅ :+ u) |- e̅ ∷ _C)
  } yield ()
  case _ => judgementError(j)
}

object eqTyping { given key as eqTyping.type = this }
def check(j: ≡[Term] ∷ Type)(using Γ: Context)(using Σ: Signature)(using d : eqTyping.type) : Result[Unit] = TODO()

object eqTelescopeTyping { given key as eqTelescopeTyping.type = this }
def check(j: ≡[List[Term]] ∷ Telescope)(using Γ: Context)(using Σ: Signature)(using d : eqTelescopeTyping.type) : Result[Unit] = TODO() 

object eqElimTyping { given key as eqElimTyping.type = this }
def check(j: Term ∷ Type |- ≡[List[Elimination]] ∷ Type)(using Γ: Context)(using Σ: Signature)(using d : eqElimTyping.type) : Result[Unit] = TODO()

// ------- magic splitter -------

def app(x: Term, t: Term) = appElim(x, ETerm(t))
def app(x: Term, f: String) = appElim(x, EProj(f))

def appElim(x: Term, e: Elimination) : Result[Term] = x match {
  case TRedux(fn, elims) => Right(TRedux(fn, elims :+ e))
  case TWhnf(WVar(idx, elims)) => Right(TWhnf(WVar(idx, elims :+ e)))
  case _ => typingError(s"Cannot apply $e to $x.")
}

extension signatureTypingOps on (self: Signature) {
  def apply(data : WData) : Result[Declaration.Data[Status.Checked, IndexedSeq]] = self(data.qn) match {
    case d : Declaration.Data[Status.Checked, IndexedSeq] => Right(d)
    case _ => typingError(s"No data schema found for ${data.qn}")
  }

  def apply(record : WRecord) : Result[Declaration.Record[Status.Checked, IndexedSeq]] = self(record.qn) match {
    case r : Declaration.Record[Status.Checked, IndexedSeq] => Right(r)
    case _ => typingError(s"No record schema found for ${record.qn}")
  }

  def apply(redux : TRedux) : Result[Declaration.Definition[Status.Checked, IndexedSeq]] = self(redux.fn) match {
    case d : Declaration.Definition[Status.Checked, IndexedSeq] => Right(d)
    case _ => typingError(s"No record schema found for ${redux.fn}")
  }
}

extension dataOps on (self: Declaration.Data[Status.Checked, IndexedSeq]) {
  def apply(name: String) : Result[Constructor] = self.cons.find(_.name == name) match {
    case Some(c) => Right(c)
    case None => typingError(s"Cannot find constructor '$name' for data ${self.qn}.")
  }
}

extension recordOps on (self: Declaration.Record[Status.Checked, IndexedSeq]) {
  def apply(name: String) : Result[Field] = self.fields.find(_.name == name) match {
    case Some(f) => Right(f)
    case None => typingError(s"Cannot find field '$name' for record ${self.qn}.")
  }
}

type Result = Either[TypingError, *]
type Level = Int

case class ∷[X, Y](x: X, y: Y)

case class ≡[X](a: X, b: X)

case class |-[X, Y](a: X, b: Y)

extension typingRelation on (x: Term) {
  def ∷ (y: Type) = new ∷(x, y)
}

extension telescopeTypingRelation on (x̅: List[Term]) {
  def ∷ (Δ: Telescope) = new ∷(x̅, Δ)
}

extension elimTypingRelation on (e̅: List[Elimination]) {
  def ∷ (_A: Type) = new ∷(e̅, _A)
}

extension eqTermTypingRelation on (e: ≡[Term]) {
  def ∷ (_A: Type) = new ∷(e, _A)
}

extension eqElimTypingRelation on (e: ≡[Elimination]) {
  def ∷ (_A: Type) = new ∷(e, _A)
}

extension equalityRelation on [X](x: X) {
  def ≡ (y: X) = new ≡(x, y)
}

extension derivationRelation on [X, Y](x: X) {
  def |- (y: Y) = new |-(x, y)
}

case class TypingError(msg: String)

def judgementError(judgement: ∷[?, ?] | |-[?, ?] | ≡[?] ) : Either[TypingError, Nothing] = typingError(s"Invalid judgement $judgement")
def typingError(msg: String) : Either[TypingError, Nothing] = Left(TypingError(msg))
