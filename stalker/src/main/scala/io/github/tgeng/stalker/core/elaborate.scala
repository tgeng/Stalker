package io.github.tgeng.stalker.core

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.common._
import io.github.tgeng.stalker.common._
import reduction._

extension elaboration on (p: Problem) {
  def elaborate(using Γ: Context)(using Σ: Signature)(using clauses: ArrayBuffer[Clause]) : Result[CaseTree] = {
    p match {
      // Done
      case ((_E1, q̅1) |-> rhs) :: _ ||| (f, q̅) ∷ _C if (q̅1.isEmpty) => for {
        _ <- Right(())
      } yield ???
    }
    ???
  }
}

private def (_E: Set[(Term /? Pattern) ∷ Type]) solve(using Γ: Context)(using Σ: Signature) : Result[Substitution[Term]] = {
  import io.github.tgeng.stalker.core.typing.checkTermsEq
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
        _ <- (ps.map(_.toTerm).map(_.subst(σ)) ≡ ws ∷ Δ).check
      } yield σ
    }
    case _ => typingError("mismatch")
  }
}

type Problem =  UserInput ||| (QualifiedName, List[CoPattern]) ∷ Type
type UserInput = List[(Set[(Term /? Pattern) ∷ Type], List[CoPattern]) |-> UncheckedRhs]

case class |||[A, B](a: A, b: B)
case class |->[Lhs, Rhs](lhs: Lhs, rhs: Rhs)
case class /?[T, P](w: T, p: P)
