package io.github.tgeng.stalker.core

import io.github.tgeng.common._

enum USuccess {
  case UPositive(context: Context, unifyingSubst: Substitution[Pattern], restoringSubst: Substitution[Pattern])
  case UNegative
}

import USuccess._

// The structure of the unification algorithm is based on "Unifiers as
// Equivalences" by Cockx et al. However, as for now only the most basic
// unification is implemented: it entails K, entails injectivity of type
// constructor (i.e. does not admit law excluded middle), does not admit
// function extensionality. A more sophisticated type-driven algorithm can be
// implemented in future to make Stalker support various useful extensions as a
// proof assistance. But this naive algorithm should already be sufficient for
// using Stalker as a general programming language supporting dependent types.

extension termUnification on (p: =?[Whnf] ∷ Type) {
  def unify(using Γ: Context)(using Σ: Signature) : Result[USuccess] = p match {
    case (u =? v) ∷ _ if u == v => positive(Γ, TODO(), TODO())
  }
}

extension termsUnification on (p: List[=?[Whnf]] ∷ Telescope) {
  def unify(using Γ: Context)(using Σ: Signature) : Result[USuccess] = p match {
    case _ => TODO()
  }
}

private def positive(context: Context, unifyingSubst: Substitution[Pattern], restoringSubst: Substitution[Pattern]) : Result[USuccess] =
  Right(UPositive(context, unifyingSubst, restoringSubst))

private val negative : Result[USuccess] = Right(UNegative)
private def failure(msg: String) : Result[USuccess] = Left(TypingError(s"Unification failure: $msg"))

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
