package io.github.tgeng.stalker.core

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.common._
import io.github.tgeng.stalker.common._
import reduction._
import typing.checkTerm
import typing.checkTermsEq
import CaseTree._
import CoPattern._
import Pattern._
import Whnf._
import Term._
import ClauseT._
import UncheckedRhs._

extension elaboration on (p: Problem) {
  def elaborate(using Γ: Context)(using Σ: Signature)(using clauses: ArrayBuffer[Clause]) : Result[CaseTree] = {
    p match {
      // User input available
      case (_P@((_E1, q̅1) |-> rhs1) :: _) ||| (f, q̅) ∷ _C => _E1.solve match {
        // Done
        case Right(σ) if q̅1.isEmpty => rhs1 match {
          case UTerm(v) => {
              val vσ = v.subst(σ)
              (vσ ∷ _C).check match {
              case Right(_) => {
                clauses.append(CheckedClause(Γ.toClosedTelescope, q̅, vσ, _C))
                Right(CTerm(vσ))
              }
              case Left(e) => Left(e)
            }
          }
          case _ => typingError("False impossible case.")
        }
        case _ => (_C, q̅1) match {
          // Intro
          case ((_F@WFunction(_A, _B)), QPattern(p) :: _) => for {
            wA <- _A.whnf 
            r <- withCtxExtendedBy(_F.argName ∷ wA) {
              for {
                wB <- _B.whnf
                _Pmod <- _P(wA)
                r <- (_Pmod ||| (f, q̅.map(_.raise(1)) :+ QPattern(PVar(0))) ∷ wB).elaborate
              } yield CLam(r)
            }
          } yield r
          // CoSplit
          case (WRecord(qn, v̅), QProj(π) :: _) => ???
          // Split
          case _ => {
            ???
          }
        }
      }
      // No user input. Try to find empty type in Γ
      case Nil ||| (f, q̅) ∷ _C => ???
    }
  }
}

private def (_E: Set[(Term /? Pattern) ∷ Type]) solve(using Γ: Context)(using Σ: Signature) : Result[Substitution[Term]] = {
  _E.foldLeft(matched(Map.empty)){ case (acc, (w /? p) ∷ _A) =>
    for {
      σ1 <- acc
      σ2 <- w / p
      σ <- σ1 ⊎ σ2
    } yield σ
  }.flatMap {
    case Right(m) => {
      val σ = Substitution.from(m)
      val _ESeq = _E.toList
      val ws = _ESeq.map{ case (w /? _) ∷ _ => w}
      val ps = _ESeq.map{ case (_ /? p) ∷ _ => p}
      val Δ = _ESeq.map{ case (_ /? _) ∷ _A => "" ∷ _A}
      for {
        // Check again to ensure forced patterns are correct.
        _ <- (ps.map(_.toTerm).map(_.subst(σ)) ≡ ws ∷ Δ).check
      } yield σ
    }
    case _ => typingError("Mismatch")
  }
}

private def (_P: UserInput) apply (_A: Type): Result[UserInput] = _P match {
  case Nil => Right(Nil)
  case ((_E, QPattern(p) :: q̅) |-> rhs) :: _P => for {
    _Pmod <- _P(_A)
  } yield ((_E.map{ case (w /? p) ∷ _B => (w.raise(1) /? p) ∷ _B } union Set((TWhnf(WVar(0, Nil)) /? p) ∷ _A) , q̅) |-> rhs) :: _Pmod
  case _ => typingError("Unexpected patterns")
}

type Problem =  UserInput ||| (QualifiedName, List[CoPattern]) ∷ Type
type UserInput = List[(Set[(Term /? Pattern) ∷ Type], List[CoPattern]) |-> UncheckedRhs]

extension applicationTypingRelation on (app : (QualifiedName, List[CoPattern])) {
  def ∷ (A: Type) = new ∷(app, A)
}

extension userInputBarBarBar on (_P : UserInput) {
  def |||(a: (QualifiedName, List[CoPattern]) ∷ Type) = new |||(_P, a)
}

extension lhsOps on (lhs: (Set[(Term /? Pattern) ∷ Type], List[CoPattern])) {
  def |->(rhs: UncheckedRhs) = new |->(lhs, rhs)
}

extension termMatchingOps on (t: Term) {
  def /?(p: Pattern) = new /?(t, p)
}

extension matchTypingRelation on (m: Term /? Pattern) {
  def ∷(_A: Type) = new ∷(m, _A)
}

case class |||[A, B](a: A, b: B)
case class |->[Lhs, Rhs](lhs: Lhs, rhs: Rhs)
case class /?[T, P](w: T, p: P)
