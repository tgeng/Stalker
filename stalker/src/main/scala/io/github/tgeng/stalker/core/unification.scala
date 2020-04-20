package io.github.tgeng.stalker.core

import scala.math.{min, max}
import scala.language.implicitConversions
import io.github.tgeng.common._
import substitutionConversion.{given _}
import io.github.tgeng.stalker.core.typing.level
import io.github.tgeng.stalker.core.typing.whnf
import io.github.tgeng.stalker.core.typing.tele

enum USuccess {
  case UPositive(context: Context, unifyingSubst: Substitution[Pattern], restoringSubst: Substitution[Pattern])
  case UNegative

  def ∘ (other: USuccess) : USuccess = (this, other) match {
    case (UPositive(c1, u1, r1), UPositive(c2, u2, r2)) => UPositive(c2, u1 ∘ u2, r2 ∘ r1)
    case (_, _) => UNegative
  }
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

import Pattern._
import Term._
import Whnf._

extension termUnification on (p: =?[Term] ∷ Type) {
  def unify(using Γ: Context)(using Σ: Signature) : Result[USuccess] = p.simpl match {
    // delete
    case (u =? v) ∷ _A if u == v => positive(
      Γ, 
      Γ.idSubst ⊎ PRefl, 
      Γ + idType(_A, u, v),
      Γ.idSubst)

    // cycle
    case (x =? y) ∷ _A if isCyclic(x, y, _A) => UNegative

    // solution
    case (TWhnf(WVar(x, Nil)) =? TWhnf(WVar(y, Nil))) ∷ _A => solution(min(x, y), TWhnf(WVar(max(x, y), Nil)), _A)
    case (TWhnf(WVar(x, Nil)) =? w) ∷ _A => solution(x, w, _A)
    case (w =? TWhnf(WVar(y, Nil))) ∷ _A => solution(y, w, _A)

    // injectivity - data constructors
    case (((u@TWhnf(WCon(c1, u̅))) =? (v@TWhnf(WCon(c2, v̅)))) ∷ (_A@WData(qn, params))) if c1 == c2 => for {
      data <- Σ getData(qn)
      con <- data(c1)
      argTys <- con.argTys.subst(params).tele
      unifier <- ((u̅ =? v̅) ∷ argTys).unify
    } yield positive(
      Γ + idTypes(argTys, u̅, v̅), 
      // Theoretically we should construct something like `congruent con`. But
      // after composing with `unifier` it should always reduce to `PRefl`.
      // Therefore, we just save the work and return `PRefl` directly. We do the
      // same below as well.
      Γ.idSubst ⊎ PRefl,
      Γ + idType(_A, u, v),
      Γ.idSubst ⊎ argTys.map(_ => PRefl)
    ) ∘ unifier

    // injectivity - type constructors
    case ((u@TWhnf(WId(_A, a1, a2))) =? (v@TWhnf(WId(_B, b1, b2)))) ∷ _U => for {
      wA <- _A.whnf
      lA <- wA.level
      w1 = List(_A, a1, a2)
      w2 = List(_B, b1, b2)
      _Γ = List("X" ∷ WUniverse(lA), "x" ∷ WVar(0, Nil), "y" ∷ WVar(1, Nil))
      unifier <- ((w1 =? w2) ∷ _Γ).unify
    } yield positive(
      Γ + idTypes(_Γ, w1, w2),
      Γ.idSubst ⊎ PRefl,
      Γ + idType(_U, u, v),
      Γ.idSubst ⊎ List(PRefl, PRefl, PRefl)
    ) ∘ unifier
    case ((u@TWhnf(WData(qn1, params1))) =? (v@TWhnf(WData(qn2, params2)))) ∷ _U if qn1 == qn2 => for {
      data <- Σ getData qn1 
      unifier <- ((params1 =? params2) ∷ data.paramTys).unify
    } yield positive(
      Γ + idTypes(data.paramTys, params1, params2),
      Γ.idSubst ⊎ PRefl,
      Γ + idType(_U, u, v),
      Γ.idSubst ⊎ data.paramTys.map(_ => PRefl)
    ) ∘ unifier
    case ((u@TWhnf(WRecord(qn1, params1))) =? (v@TWhnf(WRecord(qn2, params2)))) ∷ _U if qn1 == qn2 => for {
      record <- Σ getRecord qn1 
      unifier <- ((params1 =? params2) ∷ record.paramTys).unify
    } yield positive(
      Γ + idTypes(record.paramTys, params1, params2),
      Γ.idSubst ⊎ PRefl,
      Γ + idType(_U, u, v),
      Γ.idSubst ⊎ record.paramTys.map(_ => PRefl)
    ) ∘ unifier

    // stuck
    case (TRedux(_, _) =? _) ∷ _ | 
         (_ =? TRedux(_, _)) ∷ _ |
         (TWhnf(WFunction(_, _)) =? TWhnf(WFunction(_, _))) ∷ _ => failure(s"Cannot solve unification problem $p.")

    // absurd
    case _ => UNegative
  }

  private def simpl(using Γ: Context)(using Σ: Signature) : =?[Term] ∷ Type = p match {
    case (u =? v) ∷ _A => (simplTerm(u) =? simplTerm(v)) ∷ _A
  }
}

extension termsUnification on (p: =?[List[Term]] ∷ Telescope) {
  def unify(using Γ: Context)(using Σ: Signature) : Result[USuccess] = p match {
    case (Nil =? Nil) ∷ Nil => positive(Γ, Γ.idSubst, Γ, Γ.idSubst)
    case ((u :: u̅) =? (v :: v̅)) ∷ (_A :: _Δ) => for {
      unifier <- ((u =? v) ∷ _A.ty).unify
      restUnifier <- unifier match {
        case UNegative => Right(UNegative)
        case UPositive(context, unifyingSubst, restoringSubst) => withCtx(context) {
          for {
            _Δmod <- _Δ.subst(unifyingSubst).tele
            t <- ((u̅.map(_.subst(unifyingSubst)) =? v̅.map(_.subst(unifyingSubst))) ∷ _Δmod).unify
          } yield t
        }
      }
    } yield unifier ∘ restUnifier
  }
}

private def solution(idx: Int, t: Term, _A: Type)(using Γ: Context)(using Σ: Signature) : Result[USuccess] = {
  TODO()
}

private def isCyclic(x: Term, y: Term, _A: Type)(using Γ: Context)(using Σ: Signature) : Boolean = TODO()

private def idTypes(Δ: Telescope, u̅: List[Term], v̅: List[Term]) : List[Binding[Type]] = (Δ, u̅, v̅) match {
  case (Nil, Nil, Nil) => Nil
  case (_A :: Δ, u :: u̅, v :: v̅) => s"e${_A.name}" ∷ WId(TWhnf(_A.ty), u, v) :: idTypes(Δ, u̅, v̅)
  case _ => throw IllegalArgumentException()
}

private def idType(_A: Type, u: Term, v: Term) : Binding[Type] = "e" ∷ WId(TWhnf(_A), u, v)

private def simplTerm(tm: Term)(using Γ: Context)(using Σ: Signature) : Term = tm.whnf match {
  case Right(f@WFunction(a, b)) => TWhnf(WFunction(simplTerm(a), simplTerm(b))(f.argName))
  case Right(w: Whnf) => TWhnf(w)
  case _ => tm
}

private def positive(solutionCtx: Context, unifyingSubstFn: (given ctx: Context) => Substitution[Pattern], sourceCtx: Context, restoringSubstFn: (given ctx: Context) => Substitution[Pattern]) : USuccess = {
  val unifyingSubst = unifyingSubstFn(using solutionCtx)
  val restoringSubst = restoringSubstFn(using sourceCtx)
  if (unifyingSubst.content.size != sourceCtx.size || 
      restoringSubst.content.size != solutionCtx.size || 
      unifyingSubst.sourceContextSize != solutionCtx.size || 
      restoringSubst.sourceContextSize != sourceCtx.size) {
    throw IllegalArgumentException("Invalid unifier")
  }
  UPositive(solutionCtx, unifyingSubst, restoringSubst)
}

private given uSuccessToEither as Conversion[USuccess, Result[USuccess]] = Right(_)

private def failure(msg: String) : Result[USuccess] = Left(TypingError(s"Unification failure: $msg"))

case class =?[X](u: X, v: X)

extension unificationTermTypingRelation on (uv: =?[Term]) {
  def ∷ (ty: Type) = new ∷(uv, ty)
}

extension unificationTelescopeTypingRelation on (uvs: =?[List[Term]]) {
  def ∷ (tys: Telescope) = new ∷(uvs, tys)
}

extension termUnificationRelation on (u: Term) {
  def =? (v: Term) = new =?(u, v)
}

extension termsUnificationRelation on (u: List[Term]) {
  def =? (v: List[Term]) = new =?(u, v)
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
