package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import scala.math.max
import io.github.tgeng.common._
import Term._
import Whnf._
import Elimination._
import substitutionConversion.{given _}

def (tm: Type)level(using Γ: Context)(using Σ: Signature) : Result[Level] = tm match {
  case WUniverse(l) => Right(l + 1)
  case WFunction(_A, _B) => {
    for {
      wA <- _A.whnf
      lA <- wA.level
      _Θ = wA :: Γ
      rB <- _B.whnf(using _Θ)
      lB <- rB.level(using _Θ)
    } yield max(lA, lB)
  }
  case _D@WData(qn, u) => for {
    data <- Σ(_D)
    _ <- (u ∷ data.paramTys).check
  } yield data.level
  case _R@WRecord(qn, u) => for {
    record <- Σ(_R)
    _ <- (u ∷ record.paramsTys).check
  } yield record.level
  case WId(_A, x, y) => {
    for {
      wA <- _A.whnf
      lA <- wA.level
      _ <- (x ∷ wA).check
      _ <- (y ∷ wA).check
    } yield lA
  }
  case _ => typingError(s"$tm is not a type.")
}

def (Δ: Telescope)level(using Γ: Context)(using Σ: Signature) : Result[Level] = Δ match {
  case Nil => Right(0)
  case _A :: _Δ => for {
    lA <- _A.level
    lΔ <- _Δ.level(using _A :: Γ)
  } yield max(lA, lΔ)
}

def (eq: ≡[Type])level(using Γ: Context)(using Σ: Signature) : Result[Level] = eq match {
  case _A ≡ _B if _A == _B => _A.level
  case WFunction(_A1, _B1) ≡ WFunction(_A2, _B2) => {
    for {
      wA1 <- _A1.whnf
      wA2 <- _A2.whnf
      lA <- (wA1 ≡ wA2).level
      _Θ = wA2 :: Γ
      wB1 <- _B1.whnf(using _Θ)
      wB2 <- _B2.whnf(using _Θ)
      lB <- (wB1 ≡ wB2).level(using _Θ)
    } yield max(lA, lB)
  }
  case WVar(x, e̅1) ≡ WVar(y, e̅2) if (x == y) => (TWhnf(WVar(x, Nil)) ∷ Γ(x) |- e̅1 ≡ e̅2).level
  case WId(_A1, u1, v1) ≡ WId(_A2, u2, v2) => {
    for {
      wA1 <- _A1.whnf
      wA2 <- _A2.whnf
      l <- (wA1 ≡ wA2).level
      _ <- (u1 ≡ u2 ∷ wA1).check
      _ <- (v1 ≡ v2 ∷ wA1).check
    } yield l
  }
  case (d@WData(d1, u̅1)) ≡ WData(d2, u̅2) if d1 == d2 => for {
    data <- Σ(d)
    _ <- (u̅1 ≡ u̅2 ∷ data.paramTys).check
  } yield data.level
  case (r@WRecord(r1, u̅1)) ≡ WRecord(r2, u̅2) if r1 == r2 => for {
    record <- Σ(r)
    _ <- (u̅1 ≡ u̅2 ∷ record.paramsTys).check
  } yield record.level
  case _ => typingError(s"Cannot infer level of $eq")
}

def (elim: Term ∷ Type |- ≡[List[Elimination]])level(using Γ: Context)(using Σ: Signature) : Result[Level] = {
  elim match {
    case x ∷ _A |- e̅1 ≡ e̅2 => (for {
      _ <- (x ∷ _A).check
    } yield ()) match {
      case Right(_) => ()
      case Left(e) => return Left(e)
    }
  }
  elim match {
    case u ∷ _A |- Nil ≡ Nil => _A.level
    case u ∷ WFunction(_A, _B) |- (ETerm(v1) :: e̅1) ≡ (ETerm(v2) :: e̅2) => for {
      wA <- _A.whnf
      _ <- (v1 ≡ v2 ∷ wA).check
      wB <- _B(v1).whnf
      uv <- app(u, v1)
      l <- (uv ∷ wB |- e̅1 ≡ e̅2).level
    } yield l
    case u ∷ (r@WRecord(_, v̅)) |- (EProj(π) :: e̅1) ≡ (EProj(π1) :: e̅2) if π == π1 => for {
      record <- Σ(r)
      field <- record(π)
      wA <- field.ty(v̅ :+ u).whnf
      uπ <- app(u, π)
      l <- (uπ ∷ wA |- e̅1 ≡ e̅2).level
    } yield l
    case _ => typingError(s"Cannot infer level of $elim")
  }
}

extension checkTerm on (j: Term ∷ Type) {
  def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case _ ∷ _A => _A.level match {
        case Right(_) => ()
        case Left(e) => return Left(e)
      }
    }
    j match {
      // Types
      case _A ∷ WUniverse(l) => (for {
        wA <- _A.whnf
        lA <- wA.level
      } yield lA == l) match {
        case Right(true) => Right(())
        case _ => judgementError(j)
      }
      // Heads
      case TWhnf(WVar(idx, e̅)) ∷ _A => for {
        _ <- (TWhnf(WVar(idx, Nil)) ∷ Γ(idx) |- e̅ ∷ _A).check
      } yield ()
      case (r@TRedux(fn, e̅)) ∷ _A => for {
        definition <- Σ(r)
        _ <- (TRedux(fn, Nil) ∷ definition.ty |- e̅ ∷ _A).check
      } yield ()
      // Values
      case TWhnf(WCon(c, v̅)) ∷ (wData@WData(d, u̅)) => for {
        data <- Σ(wData)
        constructor <- data(c)     
        _ <- (u̅ ∷ data.paramTys).check
        _Δ <- constructor.argTys(v̅).tele
        _ <- (v̅ ∷ _Δ).check
      } yield ()
      case TWhnf(WRefl) ∷ WId(_A, u, v) => for {
        wA <- _A.whnf
        _ <- (u ≡ v ∷ wA).check
      } yield ()
      case _ => judgementError(j)
    }
  }
}

extension checkTerms on (j: List[Term] ∷ Telescope) {
  def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = j match {
    case Nil ∷ Nil => Right(())
    case (x :: u̅) ∷ (_A :: _Δ) => for {
      _ <- (x ∷ _A).check
      _Θ <- _Δ(x).tele
      _ <- (u̅ ∷ _Δ).check(using _Θ)
    } yield ()
    case _ => judgementError(j)
  }
}

extension checkElim on (j: Term ∷ Type |- List[Elimination] ∷ Type) {
  def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case u ∷ _A |- e̅ ∷ _C => (for {
        _ <- (u ∷ _A).check
        _ <- _C.level
      } yield ()) match {
        case Right(_) => ()
        case Left(e) => return Left(e)
      }
    }
    j match {
      case u ∷ _A |- Nil ∷ _B  => for {
        _ <- (_A ≡ _B).level
      } yield ()
      case u ∷ WFunction(_A, _B) |- (ETerm(v) :: e̅) ∷ _C => for {
        wA <- _A.whnf
        _ <- (v ∷ wA).check
        uv <- app(u, v)
        _Bv = _B(v)
        wBv <- _Bv.whnf
        _ <- (uv ∷ wBv).check
        _ <- (uv ∷ wBv |- e̅ ∷ _C).check
      } yield ()
      case u ∷ (_R@WRecord(_, v̅)) |- (EProj(π) :: e̅) ∷ _C => for {
        record <- Σ(_R)
        field <- record(π) 
        uπ <- app(u, π)
        ft <- field.ty(v̅ :+ u).whnf
        _ <- (uπ ∷ ft |- e̅ ∷ _C).check
      } yield ()
      case _ => judgementError(j)
    }
  }
}

extension checkTermEq on (j: ≡[Term] ∷ Type) {
  def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case x ≡ y ∷ _A if x == y => (for{
        _ <- _A.level
        _ <- (x ∷ _A).check
      } yield ()) match {
        case Right(_) => return Right(())
        case _ => ()
      }
      case x ≡ y ∷ _A => (for {
        _ <- _A.level
        _ <- (x ∷ _A).check
        _ <- (y ∷ _A).check
      } yield ()) match {
        case Right(_) => Right(())
        case Left(e) => return Left(e)
      }
    }
    j match {
      case (r@TRedux(f1, e̅1)) ≡ TRedux(f2, e̅2) ∷ _B if f1 == f2 => for {
        fn <- Σ(r)
        _ <- (TRedux(f1, Nil) ∷ fn.ty |- e̅1 ≡ e̅2 ∷ _B).check
      } yield ()
      // function eta rule
      case f ≡ g ∷ WFunction(_A, _B) => for {
        fx <- app(f, TWhnf(WVar(0, Nil)))
        gx <- app(g, TWhnf(WVar(0, Nil)))
        wA <- _A.whnf
        wB <- _B.whnf
        _ <- (fx ≡ gx ∷ wB).check(using wA :: Γ)
      } yield ()
      case x ≡ y ∷ _A => for {
        wX <- x.whnf
        wY <- y.whnf
        _ <- wX ≡ wY ∷ _A match {
          case x ≡ y ∷ _ if x == y => Right(())
          case x ≡ y ∷ WUniverse(l) => (x ≡ y).level match {
            case Right(inferredLevel) if inferredLevel == l => Right(())
            case _ => judgementError(j)
          }
          case WVar(x, e̅1) ≡ WVar(y, e̅2) ∷ _A if x == y => (TWhnf(WVar(x, Nil)) ∷ Γ(x) |- e̅1 ≡ e̅2 ∷ _A).check
          case WCon(c1, v̅1) ≡ WCon(c2, v̅2) ∷ (d@WData(_, u̅)) if c1 == c2 => for {
            data <- Σ(d)
            con <- data(c1)
            _ <- (u̅ ∷ data.paramTys).check
            _Δ <- con.argTys(u̅).tele
            _ <- (v̅1 ≡ v̅2 ∷ _Δ).check
          } yield ()
          case _ => judgementError(j)
        }
      } yield ()  
    }
  }
}

extension checkTermsEq on (j: ≡[List[Term]] ∷ Telescope) {
  def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case _ ≡ _ ∷ Γ => Γ.level match {
        case Right(_) => ()
        case _ => return judgementError(j)
      }
    }
    j match {
      case Nil ≡ Nil ∷ Nil => Right(())
      case (u :: u̅) ≡ (v :: v̅) ∷ (_A :: _Δ) => for {
        _ <- (u ≡ v ∷ _A).check
        _Θ <- _Δ(u).tele
        _ <- (u̅ ≡ v̅ ∷ _Θ).check(using _A :: Γ)
      } yield ()
    }
  }
}

extension checkElimEq on (j: Term ∷ Type |- ≡[List[Elimination]] ∷ Type) {
  def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case x ∷ _A |- e̅1 ≡ e̅2 ∷ _C => (for {
        _ <- (x ∷ _A).check
        _ <- _C.level
      } yield ()) match {
        case Right(_) => ()
        case Left(e) => return Left(e)
      }
    }
    j match {
      case u ∷ _A |- Nil ≡ Nil ∷ _C => (_A ≡ _C).level.map(l => ())
      case u ∷ WFunction(_A, _B) |- (ETerm(v1) :: e̅1) ≡ (ETerm(v2) :: e̅2) ∷ _C => for {
        wA <- _A.whnf
        _ <- (v1 ≡ v2 ∷ wA).check
        wB <- _B(v1).whnf
        uv <- app(u, v1)
        _ <- (uv ∷ wB |- e̅1 ≡ e̅2 ∷ _C).check
      } yield ()
      case u ∷ (r@WRecord(_, v̅)) |- (EProj(π) :: e̅1) ≡ (EProj(π1) :: e̅2) ∷ _C if π == π1 => for {
        record <- Σ(r)
        field <- record(π)
        wA <- field.ty(v̅ :+ u).whnf
        uπ <- app(u, π)
        _ <- (uπ ∷ wA |- e̅1 ≡ e̅2 ∷ _C).check
      } yield ()
      case _ => judgementError(j)
    }
  }
}

def (tm: Term).whnf(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
  case TWhnf(w) => Right(w)
  case TRedux(fn, elims) => TODO()
}

def (tms: List[Term]).tele(using Γ: Context)(using Σ: Signature) : Result[Telescope] = tms match {
  case Nil => Right(Nil)
  case tm :: rest => for {
    wTm <- tm.whnf
    wRest <- rest.tele
  } yield wTm :: wRest
}

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
  def ∷ (A: Type) = new ∷(e̅, A)
}

extension eqTermTypingRelation on (e: ≡[Term]) {
  def ∷ (A: Type) = new ∷(e, A)
}

extension eqWhnfTypingRelation on (e: ≡[Whnf]) {
  def ∷ (A: Whnf) = new ∷(e, A)
}

extension eqTelescopeTypingRelation on (e: ≡[List[Term]]) {
  def ∷ (Δ: Telescope) = new ∷(e, Δ)
}

extension eqElimsTypingRelation on (e: ≡[List[Elimination]]) {
  def ∷ (A: Type) = new ∷(e, A)
}

extension eqElimTypingRelation on (e: ≡[Elimination]) {
  def ∷ (A: Type) = new ∷(e, A)
}

extension termEqRelation on (x: Term) {
  def ≡ (y: Term) = new ≡(x, y)
}

extension typeEqRelation on (x: Type) {
  def ≡ (y: Type) = new ≡(x, y)
}

extension typesEqRelation on (x: List[Term]) {
  def ≡ (y: List[Term]) = new ≡(x, y)
}

extension elimEqRelation on (x: List[Elimination]) {
  def ≡ (y: List[Elimination]) = new ≡(x, y)
}

extension derivationRelation on [X, Y](x: X) {
  def |- (y: Y) = new |-(x, y)
}

case class TypingError(msg: String)

def judgementError(judgement: ∷[?, ?] | |-[?, ?] | ≡[?] ) : Either[TypingError, Nothing] = typingError(s"Invalid judgement $judgement")
def typingError(msg: String) : Either[TypingError, Nothing] = Left(TypingError(msg))
