package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import scala.math.max
import io.github.tgeng.common._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common._
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt.telescopeOps
import substitutionConversion.{given _}
import Term._
import Whnf._
import Elimination._
import ClauseT._
import Pattern._
import CoPattern._
import reduction.tele
import reduction.whnf

object typing {
  def (tm: Type)level(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
    case WType(l) => Right(lsuc(l))
    case WLevelType => Right(lconst(0))
    case WFunction(_A, _B) => {
      for {
        wA <- _A.ty.whnf
        lA <- wA.level
        r <- withCtxExtendedBy(_A.name ∷ wA) {
          for {
            rB <- _B.whnf
            lB <- rB.level
          } yield lmax(TWhnf(lA), TWhnf(lB))
        }
      } yield r
    }
    case WData(qn, u) => for {
      data <- Σ getData qn
      _ <- (u ∷ data.paramTys).check
    } yield data.level
    case WRecord(qn, u) => for {
      record <- Σ getRecord qn
      _ <- (u ∷ record.paramTys).check
    } yield record.level
    case WId(l, _A, x, y) => {
      for {
        wl <- l.whnf
        wA <- _A.whnf
        lA <- wA.level
        _ <- if (wl == lA) Right(())
             else typingError(s"Expect $_A to be at level $l but it's at level $lA")
        _ <- (x ∷ wA).check
        _ <- (y ∷ wA).check
      } yield lA
    }
    case WVar(idx, e̅) => (TWhnf(WVar(idx, Nil)) ∷ Γ(idx).ty |- e̅).elimLevel
    case _ => typingError(s"$tm is not a type.")
  }
  
  def (Δ: Telescope)level(using Γ: Context)(using Σ: Signature) : Result[Whnf] = Δ match {
    case Nil => Right(lconst(0))
    case _A :: _Δ => for {
      lA <- _A.ty.level
      lΔ <- _Δ.level(using Γ + _A)
    } yield lmax(TWhnf(lA), TWhnf(lΔ))
  }

  def (eq: ≡[Type])eqLevel(using Γ: Context)(using Σ: Signature) : Result[Whnf] = eq match {
    case _A ≡ _B if _A == _B => _A.level
    case WFunction(_A1, _B1) ≡ WFunction(_A2, _B2) => {
      for {
        wA1 <- _A1.ty.whnf
        wA2 <- _A2.ty.whnf
        lA <- (wA1 ≡ wA2).eqLevel
        r <- withCtxExtendedBy(_A1.name ∷ wA2) {
          for {
            wB1 <- _B1.whnf
            wB2 <- _B2.whnf
            lB <- (wB1 ≡ wB2).eqLevel
          } yield lmax(TWhnf(lA), TWhnf(lB))
        }
      } yield r
    }
    case WVar(x, e̅1) ≡ WVar(y, e̅2) if (x == y) => (TWhnf(WVar(x, Nil)) ∷ Γ(x).ty |- e̅1 ≡ e̅2).elimEqLevel
    case WId(_, _A1, u1, v1) ≡ WId(_, _A2, u2, v2) => {
      for {
        wA1 <- _A1.whnf
        wA2 <- _A2.whnf
        l <- (wA1 ≡ wA2).eqLevel
        _ <- (u1 ≡ u2 ∷ wA1).check
        _ <- (v1 ≡ v2 ∷ wA1).check
      } yield l
    }
    case WData(d1, u̅1) ≡ WData(d2, u̅2) if d1 == d2 => for {
      data <- Σ getData d1
      _ <- (u̅1 ≡ u̅2 ∷ data.paramTys).check
    } yield data.level
    case WRecord(r1, u̅1) ≡ WRecord(r2, u̅2) if r1 == r2 => for {
      record <- Σ getRecord r1
      _ <- (u̅1 ≡ u̅2 ∷ record.paramTys).check
    } yield record.level
    case _ => typingError(s"Cannot infer level of $eq")
  }

  def (j: Term ∷ Type |- List[Elimination])elimLevel(using Γ: Context)(using Σ: Signature) : Result[Whnf] = {
    j match {
      case u ∷ _A |- Nil  => _A match {
        case WType(l) => l.whnf
        case _ => typingError(s"Expected $u to be a type (whose type would be a universe), but its type is $_A.")
      }
      case u ∷ WFunction(_A, _B) |- (ETerm(v) :: e̅) => for {
        wA <- _A.ty.whnf
        _ <- (v ∷ wA).check
        uv <- u.app(v)
        _Bv = _B.substHead(v)
        wBv <- _Bv.whnf
        _ <- (uv ∷ wBv).check
        r <- (uv ∷ wBv |- e̅).elimLevel
      } yield r
      case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅) => for {
        record <- Σ getRecord r
        field <- record(π) 
        uπ <- u.app(π)
        ft <- field.ty.substHead(v̅ :+ u).whnf
        r <- (uπ ∷ ft |- e̅).elimLevel
      } yield r
      case u ∷ _A |- elims => typingError(s"Invalid application of $elims to $u of type $_A.")
    }
  }

  def (elim: Term ∷ Type |- ≡[List[Elimination]])elimEqLevel(using Γ: Context)(using Σ: Signature) : Result[Whnf] = {
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
        wA <- _A.ty.whnf
        _ <- (v1 ≡ v2 ∷ wA).check
        wB <- _B.substHead(v1).whnf
        uv <- u.app(v1)
        l <- (uv ∷ wB |- e̅1 ≡ e̅2).elimEqLevel
      } yield l
      case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅1) ≡ (EProj(π1) :: e̅2) if π == π1 => for {
        record <- Σ getRecord r
        field <- record(π)
        wA <- field.ty.substHead(v̅ :+ u).whnf
        uπ <- u.app(π)
        l <- (uπ ∷ wA |- e̅1 ≡ e̅2).elimEqLevel
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
        case _A ∷ WType(l) => for {
          wl <- l.whnf
          wA <- _A.whnf
          lA <- wA.level
          _ <- lA == wl match {
            case true => Right(())
            case false => typingError(s"Expected $_A to be at level $l, but it's at level $lA.")
          }
        } yield ()
        // Heads
        case TWhnf(v@WVar(idx, Nil)) ∷ _A => 
          if (Γ(idx).ty == _A) Right(())
          else typingError(s"Variable $v is not of type $_A but of type ${Γ(idx).ty}.")
        case TWhnf(WVar(idx, e̅)) ∷ _A => for {
          _ <- (TWhnf(WVar(idx, Nil)) ∷ Γ(idx).ty |- e̅ ∷ _A).check
        } yield ()
        case TRedux(fn, e̅) ∷ _A => for {
          definition <- Σ getDefinition fn
          _ <- (TRedux(fn, Nil) ∷ definition.ty |- e̅ ∷ _A).check
        } yield ()
        // Values
        case TWhnf(WCon(c, v̅)) ∷ WData(d, u̅) => for {
          data <- Σ getData d
          constructor <- data(c)     
          _ <- (u̅ ∷ data.paramTys).check
          _Δ <- constructor.argTys.substHead(v̅).tele
          _ <- (v̅ ∷ _Δ).check
        } yield ()
        case TWhnf(WRefl) ∷ WId(_, _A, u, v) => for {
          wA <- _A.whnf
          _ <- (u ≡ v ∷ wA).check
        } yield ()
        // Level
        case TWhnf(l) ∷ WLevelType => Right(())
        case tm ∷ ty => typingError(s"Expected $tm to be of type $ty.")
      }
    }
  }
  
  extension checkTerms on (j: List[Term] ∷ Telescope) {
    def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = j match {
      case Nil ∷ Nil => Right(())
      case (x :: u̅) ∷ (_A :: _Δ) => for {
        _ <- (x ∷ _A.ty).check
        _Θ <- _Δ.substHead(x).tele
        _ <- (u̅ ∷ _Θ).check(using Γ + _A)
      } yield ()
      case tms ∷ tys => typingError(s"Mismatched length when checking types of $tms against $tys")
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
          _ <- (_A ≡ _B).eqLevel
        } yield ()
        case u ∷ WFunction(_A, _B) |- (ETerm(v) :: e̅) ∷ _C => for {
          wA <- _A.ty.whnf
          _ <- (v ∷ wA).check
          uv <- u.app(v)
          _Bv = _B.substHead(v)
          wBv <- _Bv.whnf
          _ <- (uv ∷ wBv).check
          _ <- (uv ∷ wBv |- e̅ ∷ _C).check
        } yield ()
        case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅) ∷ _C => for {
          record <- Σ getRecord r
          field <- record(π) 
          uπ <- u.app(π)
          ft <- field.ty.substHead(v̅ :+ u).whnf
          _ <- (uπ ∷ ft |- e̅ ∷ _C).check
        } yield ()
        case u ∷ _A |- elims ∷ _C => typingError(s"Invalid application of $elims to $u of type $_A.")
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
        case TRedux(f1, e̅1) ≡ TRedux(f2, e̅2) ∷ _B if f1 == f2 => for {
          fn <- Σ getDefinition f1
          _ <- (TRedux(f1, Nil) ∷ fn.ty |- e̅1 ≡ e̅2 ∷ _B).check
        } yield ()
        // function eta rule
        case f ≡ g ∷ WFunction(_A, _B) => for {
          fx <- f.app(TWhnf(WVar(0, Nil)))
          gx <- g.app(TWhnf(WVar(0, Nil)))
          wA <- _A.ty.whnf
          wB <- _B.whnf
          _ <- (fx ≡ gx ∷ wB).check(using Γ + _A.name ∷ wA)
        } yield ()
        case x ≡ y ∷ _A => for {
          wX <- x.whnf
          wY <- y.whnf
          _ <- wX ≡ wY ∷ _A match {
            case x ≡ y ∷ _ if x == y => Right(())
            case x ≡ y ∷ WType(l) => for {
              inferredL <- (x ≡ y).eqLevel
              wl <- l.whnf
              _ <- inferredL == wl match {
                case true => Right(())
                case false => typingError(s"Expected $x ≡ $y at level $l but it's at level $inferredL.")
              }
            } yield ()
            case WVar(x, e̅1) ≡ WVar(y, e̅2) ∷ _A if x == y => (TWhnf(WVar(x, Nil)) ∷ Γ(x).ty |- e̅1 ≡ e̅2 ∷ _A).check
            case WCon(c1, v̅1) ≡ WCon(c2, v̅2) ∷ WData(d, u̅) if c1 == c2 => for {
              data <- Σ getData d
              con <- data(c1)
              _ <- (u̅ ∷ data.paramTys).check
              _Δ <- con.argTys.substHead(u̅).tele
              _ <- (v̅1 ≡ v̅2 ∷ _Δ).check
            } yield ()
            case _ => typingError(s"Cannot decide if $x and $y of type $_A are computationally equivalent.")
          }
        } yield ()  
      }
    }
  }
  
  extension checkTermsEq on (j: ≡[List[Term]] ∷ Telescope) {
    def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
      j match {
        case _ ≡ _ ∷ _Δ => _Δ.level match {
          case Right(_) => ()
          case Left(e) => return Left(e)
        }
      }
      j match {
        case Nil ≡ Nil ∷ Nil => Right(())
        case (u :: u̅) ≡ (v :: v̅) ∷ (_A :: _Δ) => for {
          _ <- (u ≡ v ∷ _A.ty).check
          _Θ <- _Δ.substHead(u).tele
          _ <- (u̅ ≡ v̅ ∷ _Θ).check(using Γ + _A)
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
        case u ∷ _A |- Nil ≡ Nil ∷ _C => (_A ≡ _C).eqLevel.map(l => ())
        case u ∷ WFunction(_A, _B) |- (ETerm(v1) :: e̅1) ≡ (ETerm(v2) :: e̅2) ∷ _C => for {
          wA <- _A.ty.whnf
          _ <- (v1 ≡ v2 ∷ wA).check
          wB <- _B.substHead(v1).whnf
          uv <- u.app(v1)
          _ <- (uv ∷ wB |- e̅1 ≡ e̅2 ∷ _C).check
        } yield ()
        case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅1) ≡ (EProj(π1) :: e̅2) ∷ _C if π == π1 => for {
          record <- Σ getRecord r
          field <- record(π)
          wA <- field.ty.substHead(v̅ :+ u).whnf
          uπ <- u.app(π)
          _ <- (uπ ∷ wA |- e̅1 ≡ e̅2 ∷ _C).check
        } yield ()
        case u ∷ _A |- elims1 ≡ elims2 ∷ _C => typingError(s"Cannot decide if applying $elims1 and $elims1 to $u of type $_A are computationally equivalent.")
      }
    }
  }
}

case class ∷[X, Y](x: X, y: Y) {
  override def toString = s"$x ∷ $y"
}

case class ≡[X](a: X, b: X) {
  override def toString = s"$a ≡ $b"
}

case class |-[X, Y](a: X, b: Y) {
  override def toString = s"$a |- $b"
}

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

extension caseTreeTypingRelation on (Q: CaseTree) {
  def ∷ (A: Type) = new ∷(Q, A)
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

extension resultFilter on [T](r: Result[T]) {
  def withFilter(p : T => Boolean) : Result[T] = r match {
    case Right(t) if (p(t)) => Right(t)
    case Right(t) => typingError(s"Result $t does not satisfy predicate $p")
    case e => e
  }
}