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
import reduction.toWhnfs
import reduction.toWhnf
import reduction.reduceLevel

import io.github.tgeng.common.debug._

object typing {
  def (tm: Term)level(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
    case TWhnf(w) => w.level
    case TRedux(qn, Nil) =>
      for definition <- Σ getDefinition qn
          r <- definition.ty match {
            case WType(l) => l.toWhnf
            case w => typingError(e"Expect type of $qn to be a type but it's $w.")
          }
      yield r
    case TRedux(qn, e̅) => 
      for definition <- Σ getDefinition qn
          r <- (TRedux(qn, Nil) ∷ definition.ty |- e̅).elimLevel
      yield r
  }

  def (tm: Type)level(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
    case WType(l) => Right(lsuc(l))
    case WLevel => Right(lconst(0))
    case WFunction(_A, _B) => {
      for {
        lA <- _A.ty.level
        wA <- _A.ty.toWhnf
        r <- withCtxExtendedBy(_A.name ∷ wA) {
          for {
            lB <- _B.level
          } yield lmax(TWhnf(lA), TWhnf(lB))
        }
      } yield r
    }
    case WData(qn, u) => for {
      data <- Σ getData qn
      _ <- (u ∷ data.paramTys).checkTerms
      l <- extractLevel(data.ty)
    } yield l
    case WRecord(qn, u) => for {
      record <- Σ getRecord qn
      _ <- (u ∷ record.paramTys).checkTerms
      l <- extractLevel(record.ty)
    } yield l
    case WId(l, _A, x, y) => {
      for {
        wl <- l.toWhnf
        lA <- _A.level
        wA <- _A.toWhnf
        _ <- if (wl == lA) Right(())
             else typingError(e"Expect $_A to be at level $l but it's at level $lA")
        _ <- (x ∷ wA).check
        _ <- (y ∷ wA).check
      } yield lA
    }
    case WVar(idx, Nil) => Γ(idx).ty match {
      case WType(l) => l.toWhnf
      case t => {
        println(Γ)
        typingError(e"${Γ(idx).name} is not a type but a $t.")
      }
    }
    case WVar(idx, e̅) => (TWhnf(WVar(idx, Nil)) ∷ Γ(idx).ty |- e̅).elimLevel
    case _ => typingError(e"$tm is not a type.")
  } flatMap { _.reduceLevel }

  def (Δ: List[Binding[Term]])levelBound(using Γ: Context)(using Σ: Signature) : Result[Option[Whnf]] = promoteLevelBound(Δ.levelBoundImpl)

  private def (Δ: List[Binding[Term]])levelBoundImpl(using Γ: Context)(using Σ: Signature) : Result[Whnf] = Δ match {
    case Nil => Right(lconst(0))
    case _A :: _Δ => for {
      lA <- _A.ty.level
      wA <- _A.ty.toWhnf
      lΔ <- _Δ.levelBoundImpl(using Γ + _A.name ∷ wA)
    } yield lmax(TWhnf(lA.raise(_Δ.size)), TWhnf(lΔ))
  } flatMap { _.reduceLevel }

  def (Δ: Telescope)teleLevelBound(using Γ: Context)(using Σ: Signature) : Result[Option[Whnf]] = promoteLevelBound(Δ.teleLevelBoundImpl)

  def (Δ: Telescope)teleLevelBoundImpl(using Γ: Context)(using Σ: Signature) : Result[Whnf] = Δ match {
    case Nil => Right(lconst(0))
    case _A :: _Δ => for {
      lA <- _A.ty.level
      lΔ <- _Δ.teleLevelBoundImpl(using Γ + _A)
    } yield lmax(TWhnf(lA.raise(_Δ.size)), TWhnf(lΔ))
  } flatMap { _.reduceLevel }

  private def promoteLevelBound(l : Result[Whnf])(using Γ: Context) : Result[Option[Whnf]] = {
    for lb <- l
        r <- {
          val freeVars = lb.freeVars
          if ((0 until Γ.size - 1).exists(freeVars.contains(_))) {
            Right(None)
          } else {
            Right(Some(lb.raise(-Γ.size + 1)))
          }
        }
    yield r
  }


  def (eq: ≡[Type])eqLevel(using Γ: Context)(using Σ: Signature) : Result[Whnf] = eq match {
    case _A ≡ _B if _A == _B => _A.level
    case WFunction(_A1, _B1) ≡ WFunction(_A2, _B2) => {
      for {
        wA1 <- _A1.ty.toWhnf
        wA2 <- _A2.ty.toWhnf
        lA <- (wA1 ≡ wA2).eqLevel
        r <- withCtxExtendedBy(_A1.name ∷ wA2) {
          for {
            wB1 <- _B1.toWhnf
            wB2 <- _B2.toWhnf
            lB <- (wB1 ≡ wB2).eqLevel
          } yield lmax(TWhnf(lA), TWhnf(lB))
        }
      } yield r
    }
    case WVar(x, e̅1) ≡ WVar(y, e̅2) if (x == y) => (TWhnf(WVar(x, Nil)) ∷ Γ(x).ty |- e̅1 ≡ e̅2).elimEqLevel
    case WId(_, _A1, u1, v1) ≡ WId(_, _A2, u2, v2) => {
      for {
        wA1 <- _A1.toWhnf
        wA2 <- _A2.toWhnf
        l <- (wA1 ≡ wA2).eqLevel
        _ <- (u1 ≡ u2 ∷ wA1).checkEq
        _ <- (v1 ≡ v2 ∷ wA1).checkEq
      } yield l
    }
    case WData(d1, u̅1) ≡ WData(d2, u̅2) if d1 == d2 => for {
      data <- Σ getData d1
      _ <- (u̅1 ≡ u̅2 ∷ data.paramTys).check
      l <- extractLevel(data.ty)
    } yield l
    case WRecord(r1, u̅1) ≡ WRecord(r2, u̅2) if r1 == r2 => for {
      record <- Σ getRecord r1
      _ <- (u̅1 ≡ u̅2 ∷ record.paramTys).check
      l <- extractLevel(record.ty)
    } yield l
    case WType(l1) ≡ WType(l2) => 
      for wl1 <- l1.toWhnf
          wl2 <- l2.toWhnf
          r <- wl1 == wl2 match {
            case true => Right(wl1)
            case false => typingError(e"Expected ${l1 ≡ l2} but they are not equal.")
          }
      yield r
    case _ => typingError(e"Cannot infer level of $eq")
  } flatMap { _.reduceLevel }

  def (j: Term ∷ Type |- List[Elimination])elimLevel(using Γ: Context)(using Σ: Signature) : Result[Whnf] = {
    j match {
      case u ∷ _A |- Nil  => _A match {
        case WType(l) => l.toWhnf
        case _ => typingError(e"Expected $u to be a type (whose type would be a Type at some level), but its type is $_A.")
      }
      case u ∷ WFunction(_A, _B) |- (ETerm(v) :: e̅) => for {
        wA <- _A.ty.toWhnf
        _ <- (v ∷ wA).check
        uv <- u.app(v)
        _Bv = _B.substHead(v)
        wBv <- _Bv.toWhnf
        r <- (uv ∷ wBv |- e̅).elimLevel
      } yield r
      case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅) => for {
        record <- Σ getRecord r
        field <- record(π) 
        uπ <- u.app(π)
        ft <- field.ty.substHead(v̅ :+ u).toWhnf
        r <- (uπ ∷ ft |- e̅).elimLevel
      } yield r
      case u ∷ _A |- elims => typingError(e"Invalid application of $elims to $u of type $_A.")
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
        wA <- _A.ty.toWhnf
        _ <- (v1 ≡ v2 ∷ wA).checkEq
        wB <- _B.substHead(v1).toWhnf
        uv <- u.app(v1)
        l <- (uv ∷ wB |- e̅1 ≡ e̅2).elimEqLevel
      } yield l
      case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅1) ≡ (EProj(π1) :: e̅2) if π == π1 => for {
        record <- Σ getRecord r
        field <- record(π)
        wA <- field.ty.substHead(v̅ :+ u).toWhnf
        uπ <- u.app(π)
        l <- (uπ ∷ wA |- e̅1 ≡ e̅2).elimEqLevel
      } yield l
      case _ => typingError(e"Cannot infer level of $elim")
    }
  } flatMap { _.reduceLevel }
  
  def (j: Term ∷ Type)check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case _ ∷ _A => _A.level match {
        case Right(_) => ()
        case Left(e) => return Left(e)
      }
    }
    j match {
      // Types
      case _A ∷ WType(l) => for {
        wl <- l.toWhnf
        lA <- _A.level
        _ <- lA == wl match {
          case true => Right(())
          case false => typingError(e"Expect $_A to be at level $l, but it's at level $lA.")
        }
      } yield ()
      // Heads
      case TWhnf(v@WVar(idx, Nil)) ∷ _A => 
        if (Γ(idx).ty == _A) Right(())
        else typingError(e"Variable $v is not of type $_A but of type ${Γ(idx).ty}.")
      case TWhnf(WVar(idx, e̅)) ∷ _A => for {
        _ <- (TWhnf(WVar(idx, Nil)) ∷ Γ(idx).ty |- e̅ ∷ _A).checkElim
      } yield ()
      case TRedux(fn, e̅) ∷ _A => for {
        definition <- Σ getDefinition fn
        _ <- (TRedux(fn, Nil) ∷ definition.ty |- e̅ ∷ _A).checkElim
      } yield ()
      // Values
      case TWhnf(WCon(c, v̅)) ∷ WData(d, u̅) => for {
        data <- Σ getData d
        constructor <- data(c)     
        _ <- (u̅ ∷ data.paramTys).checkTerms
        _Δ <- constructor.argTys.substHead(u̅).toWhnfs
        _ <- (v̅ ∷ _Δ).checkTerms
      } yield ()
      case TWhnf(WRefl) ∷ WId(_, _A, u, v) => for {
        wA <- _A.toWhnf
        _ <- (u ≡ v ∷ wA).checkEq
      } yield ()
      // Level
      case TWhnf(l) ∷ WLevel => Right(())
      case tm ∷ ty => typingError(e"Expected $tm to be of type $ty.")
    }
  }
  
  def (j: List[Term] ∷ Telescope)checkTerms(using Γ: Context)(using Σ: Signature) : Result[Unit] = j match {
    case Nil ∷ Nil => Right(())
    case (x :: u̅) ∷ (_A :: _Δ) => for {
      _ <- (x ∷ _A.ty).check
      _Θ <- _Δ.substHead(x).toWhnfs
      _ <- (u̅ ∷ _Θ).checkTerms
    } yield ()
    case tms ∷ tys => typingError(e"Mismatched length when checking types of $tms against $tys")
  }
  
  def (j: Term ∷ Type |- List[Elimination] ∷ Type)checkElim(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
    j match {
      case u ∷ _A |- Nil ∷ _B  => for {
        _ <- (_A ≡ _B).eqLevel
      } yield ()
      case u ∷ WFunction(_A, _B) |- (ETerm(v) :: e̅) ∷ _C => for {
        wA <- _A.ty.toWhnf
        _ <- (v ∷ wA).check
        uv <- u.app(v)
        _Bv = _B.substHead(v)
        wBv <- _Bv.toWhnf
        _ <- (uv ∷ wBv |- e̅ ∷ _C).checkElim
      } yield ()
      case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅) ∷ _C => for {
        record <- Σ getRecord r
        field <- record(π) 
        uπ <- u.app(π)
        ft <- field.ty.substHead(v̅ :+ u).toWhnf
        _ <- (uπ ∷ ft |- e̅ ∷ _C).checkElim
      } yield ()
      case u ∷ _A |- elims ∷ _C => typingError(e"Invalid application of $elims to $u of type $_A.")
    }
  }
  
  def (j: ≡[Term] ∷ Type)checkEq(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
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
      case l1 ≡ l2 ∷ WLevel =>
        for wl1 <- l1.toWhnf
            wl2 <- l2.toWhnf
            _ <- wl1 == wl2 match {
              case true => Right(())
              case false => typingError(e"Expected ${l1 ≡ l2} but they are not equal.")
            }
        yield ()
      case TRedux(f1, e̅1) ≡ TRedux(f2, e̅2) ∷ _B if f1 == f2 => for {
        fn <- Σ getDefinition f1
        _ <- (TRedux(f1, Nil) ∷ fn.ty |- e̅1 ≡ e̅2 ∷ _B).checkElimEq
      } yield ()
      // function eta rule
      case f ≡ g ∷ WFunction(_A, _B) => for {
        fx <- f.app(TWhnf(WVar(0, Nil)))
        gx <- g.app(TWhnf(WVar(0, Nil)))
        wA <- _A.ty.toWhnf
        wB <- _B.toWhnf
        _ <- (fx ≡ gx ∷ wB).checkEq(using Γ + _A.name ∷ wA)
      } yield ()
      case x ≡ y ∷ _A => for {
        wX <- x.toWhnf
        wY <- y.toWhnf
        _ <- wX ≡ wY ∷ _A match {
          case x ≡ y ∷ _ if x == y => Right(())
          case x ≡ y ∷ WType(l) => for {
            inferredL <- (x ≡ y).eqLevel
            wl <- l.toWhnf
            _ <- inferredL == wl match {
              case true => Right(())
              case false => typingError(e"Expected ${x ≡ y} at level $l but it's at level $inferredL.")
            }
          } yield ()
          case WVar(x, e̅1) ≡ WVar(y, e̅2) ∷ _A if x == y => (TWhnf(WVar(x, Nil)) ∷ Γ(x).ty |- e̅1 ≡ e̅2 ∷ _A).checkElimEq
          case WCon(c1, v̅1) ≡ WCon(c2, v̅2) ∷ WData(d, u̅) if c1 == c2 => for {
            data <- Σ getData d
            con <- data(c1)
            _ <- (u̅ ∷ data.paramTys).checkTerms
            _Δ <- con.argTys.substHead(u̅).toWhnfs
            _ <- (v̅1 ≡ v̅2 ∷ _Δ).check
          } yield ()
          case _ => typingError(e"Cannot decide if $x and $y of type $_A are computationally equivalent.")
        }
      } yield ()  
    }
  }
  
  extension checkTermsEq on (j: ≡[List[Term]] ∷ Telescope) {
    def check(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
      j match {
        case _ ≡ _ ∷ _Δ => _Δ.teleLevelBound match {
          case Right(_) => ()
          case Left(e) => return Left(e)
        }
      }
      j match {
        case Nil ≡ Nil ∷ Nil => Right(())
        case (u :: u̅) ≡ (v :: v̅) ∷ (_A :: _Δ) => for {
          _ <- (u ≡ v ∷ _A.ty).checkEq
          _Θ <- _Δ.substHead(u).toWhnfs
          _ <- (u̅ ≡ v̅ ∷ _Θ).check(using Γ + _A)
        } yield ()
      }
    }
  }
  
  def (j: Term ∷ Type |- ≡[List[Elimination]] ∷ Type)checkElimEq(using Γ: Context)(using Σ: Signature) : Result[Unit] = {
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
        wA <- _A.ty.toWhnf
        _ <- (v1 ≡ v2 ∷ wA).checkEq
        wB <- _B.substHead(v1).toWhnf
        uv <- u.app(v1)
        _ <- (uv ∷ wB |- e̅1 ≡ e̅2 ∷ _C).checkElimEq
      } yield ()
      case u ∷ WRecord(r, v̅) |- (EProj(π) :: e̅1) ≡ (EProj(π1) :: e̅2) ∷ _C if π == π1 => for {
        record <- Σ getRecord r
        field <- record(π)
        wA <- field.ty.substHead(v̅ :+ u).toWhnf
        uπ <- u.app(π)
        _ <- (uπ ∷ wA |- e̅1 ≡ e̅2 ∷ _C).checkElimEq
      } yield ()
      case u ∷ _A |- elims1 ≡ elims2 ∷ _C => typingError(e"Cannot decide if applying $elims1 and $elims1 to $u of type $_A are computationally equivalent.")
    }
  }

  private def extractLevel(ty: Type)(using Γ: Context)(using Σ: Signature) : Result[Type] =
    for r <- ty match {
      case WType(l) => for l <- l.toWhnf yield l
      case _ => typingError(e"$ty should be equivalent to a type at some level.")
    } 
    yield r
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
    case Right(t) => typingError(e"Result $t does not satisfy predicate $p")
    case e => e
  }
}