package io.github.tgeng.stalker.core

import io.github.tgeng.common._

enum USuccess {
  case UPositive(context: Context, unifyingSubst: Substitution[Pattern], restoringSubst: Substitution[Pattern])
  case UNegative
}

import USuccess._

extension unification on (p: =?[Whnf] ∷ Type) {
  def unify(using Γ: Context)(using Σ: Signature) : Result[USuccess] = p match {
    case _ => TODO()
  }
}

case class =?[X](u: X, v: X)

extension unificationTypingRelation on (uv: =?[Whnf]) {
  def ∷ (ty: Type) = new ∷(uv, ty)
}

extension unificationRelation on (u: Whnf) {
  def =? (v: Whnf) = new =?(u, v)
}

// extension uSuccessAssumption on (self: Result[USuccess]) {
//   def asPositive : Result[(Context, Substitution[Pattern], Substitution[Pattern])] = self match {
//     case Right(Positive(c, u, r)) => Right(c, u, r)
//     case Right(Negative) => typingError(s"Cannot solve the unification problem")
//     case Left(e) => Left(e)
//   }
  
//   def asNegative : Result[Unit] = self match {
//     case Right(Negative) => Right(())
//     case Right(Positive(_, _, _)) => typingError(s"Expect conflict for unification problem")
//     case Left(e) => Left(e)
//   }
// }
