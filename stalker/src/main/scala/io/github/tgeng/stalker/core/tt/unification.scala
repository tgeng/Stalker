package io.github.tgeng.stalker.core.tt

import scala.collection.immutable.ArraySeq
import scala.collection.mutable.HashSet
import scala.collection.mutable.ArrayBuffer
import scala.math.{min, max}
import scala.language.implicitConversions
import io.github.tgeng.common._
import io.github.tgeng.stalker.common.Error._
import io.github.tgeng.stalker.common.QualifiedName
import typing.level
import reduction.toWhnf
import reduction.toWhnfs
import substitutionConversion.{given _}
import debug._

enum UResult {
  case UPositive(context: Context, unifyingSubst: Substitution[Pattern], restoringSubst: Substitution[Pattern])
  case UNegative
  case UInconclusive(ty: Type, u: Term, v: Term)

  def ∘ (other: UResult) : UResult = (this, other) match {
    case (UPositive(c1, u1, r1), UPositive(c2, u2, r2)) => UPositive(c2, u1 ∘ u2, r2 ∘ r1)
    case (_, _) => UNegative
  }

  def ↑ (Δ: Telescope)(using Γ: Context)(using Σ: Signature) : Result[UResult] = this match {
    case (UPositive(_Γ, σ, τ)) => for {
      _Δ <- Δ.subst(σ).toWhnfs
    } yield positive(
      _Γ + _Δ,
      σ extendBy _Δ,
      Γ + Δ,
      τ extendBy Δ
    ) 
    case _ => UNegative
  }
}

import UResult._

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
  def unify(using Γ: Context)(using Σ: Signature) : Result[UResult] = p.simpl match {
    // delete
    case (u =? v) ∷ _A if u == v => positive(
      Γ, 
      Substitution.id[Pattern] ⊎ PRefl, 
      Γ + idType(_A, u, v),
      Substitution.id[Pattern].drop(1))

    // cycle
    case (x =? y) ∷ _A if isCyclic(x, y) => UNegative

    // solution
    case (TWhnf(WVar(x, Nil)) =? TWhnf(WVar(y, Nil))) ∷ _A => solution(min(x, y), TWhnf(WVar(max(x, y), Nil)), _A)
    case (TWhnf(WVar(x, Nil)) =? w) ∷ _A => solution(x, w, _A)
    case (w =? TWhnf(WVar(y, Nil))) ∷ _A => solution(y, w, _A)

    // injectivity - data constructors
    case (((u@TWhnf(WCon(c1, u̅))) =? (v@TWhnf(WCon(c2, v̅)))) ∷ (_A@WData(qn, params))) if c1 == c2 => for {
      data <- Σ getData(qn)
      con <- data(c1)
      argTys <- con.allArgTys.substHead(params).toWhnfs
      unifier <- ((u̅ ++ con.refls =? v̅ ++ con.refls) ∷ argTys).unify
    } yield positive(
      Γ + idTypes(argTys, u̅, v̅), 
      // Theoretically we should construct something like `congruent con`. But
      // after composing with `unifier` it should always reduce to `PRefl`.
      // Therefore, we just save the work and return `PRefl` directly. We do the
      // same below as well.
      Substitution.id[Pattern].drop(argTys.size) ⊎ PRefl,
      Γ + idType(_A, u, v),
      Substitution.id[Pattern].drop(1) ⊎ argTys.map(_ => PRefl)
    ) ∘ unifier

    // injectivity - type constructors
    case ((u@TWhnf(WId(_, _A, a1, a2))) =? (v@TWhnf(WId(_, _B, b1, b2)))) ∷ _U => for {
      lA <- _A.level
      wA <- _A.toWhnf
      w1 = List(_A, a1, a2)
      w2 = List(_B, b1, b2)
      _Γ = List("X" ∷ WType(TWhnf(lA)), "x" ∷ WVar(0, Nil), "y" ∷ WVar(1, Nil))
      unifier <- ((w1 =? w2) ∷ _Γ).unify
    } yield positive(
      Γ + idTypes(_Γ, w1, w2),
      Substitution.id[Pattern].drop(_Γ.size) ⊎ PRefl,
      Γ + idType(_U, u, v),
      Substitution.id[Pattern].drop(1) ⊎ List(PRefl, PRefl, PRefl)
    ) ∘ unifier
    case ((u@TWhnf(WData(qn1, params1))) =? (v@TWhnf(WData(qn2, params2)))) ∷ _U if qn1 == qn2 => for {
      data <- Σ getData qn1 
      unifier <- ((params1 =? params2) ∷ data.paramTys).unify
    } yield positive(
      Γ + idTypes(data.paramTys, params1, params2),
      Substitution.id[Pattern].drop(data.paramTys.size) ⊎ PRefl,
      Γ + idType(_U, u, v),
      Substitution.id[Pattern].drop(1) ⊎ data.paramTys.map(_ => PRefl)
    ) ∘ unifier
    case ((u@TWhnf(WRecord(qn1, params1))) =? (v@TWhnf(WRecord(qn2, params2)))) ∷ _U if qn1 == qn2 => for {
      record <- Σ getRecord qn1 
      unifier <- ((params1 =? params2) ∷ record.paramTys).unify
    } yield positive(
      Γ + idTypes(record.paramTys, params1, params2),
      Substitution.id[Pattern].drop(record.paramTys.size) ⊎ PRefl,
      Γ + idType(_U, u, v),
      Substitution.id[Pattern].drop(1) ⊎ record.paramTys.map(_ => PRefl)
    ) ∘ unifier

    // stuck
    case (TRedux(_, _) =? _) ∷ _ | 
         (_ =? TRedux(_, _)) ∷ _ |
         (TWhnf(WFunction(_, _)) =? TWhnf(WFunction(_, _))) ∷ _ => failure(p)

    // absurd
    case _ => UNegative
  }

  private def simpl(using Γ: Context)(using Σ: Signature) : =?[Term] ∷ Type = p match {
    case (u =? v) ∷ _A => (simplTerm(u) =? simplTerm(v)) ∷ _A
  }

  private def solution(x: Int, t: Term, A: Type)(using Γ: Context)(using Σ: Signature) : Result[UResult] = {
    // permutation without the final id type for x = t
    val permutation = rearrange(x)
    if (t.freeVars.exists(_ <= x)) {
      // equality covers the case where x appears free in t
      return failure(p)
    }
  
    // permutation with the id type x = t placed right after ("after" = "on the left", since permutation, like context, starts from right) x
    val permutationWithIdType = permutation(x) +: permutation.map(i => if (i < permutation(x)) i else i + 1)
    val shuffler@UPositive(_Γ, σ, τ) = shuffle(Γ + idType(A, TWhnf(WVar(x, Nil)), t), permutationWithIdType)
  
    val _x = permutation(x) + 1 // shifted because the id type `x = t` is inserted on the left of `x`

    // There seems to be a bug with Dotty 0.24. The type for _Θ is needed for it to compile.
    val (_Θ : Context, _A, xEqT :: _Δ) = _Γ.splitAt(_x)

    val _Θmod =  _Θ + _A + xEqT
  
    val tσ = t.subst(σ.drop(1)/* drop the subst term for the Id type `x=t` since t is in a context without it */).raise(-(_x + 1))
    for {
      unifier <- withCtx(_Θmod) { 
        positive(
          _Θ,
          Substitution.id[Pattern] ⊎ PForced(tσ) ⊎ PRefl,
          _Θmod,
          Substitution.id[Pattern].drop(2)
        ) ↑ _Δ
      }
    } yield shuffler ∘ unifier
  }
}

extension termsUnification on (p: =?[List[Term]] ∷ Telescope) {
  def unify(using Γ: Context)(using Σ: Signature) : Result[UResult] = p match {
    case (Nil =? Nil) ∷ Nil => positive(Γ, Substitution.id, Γ, Substitution.id)
    case ((u :: u̅) =? (v :: v̅)) ∷ (_A :: _Δ) => for {
      unifier <- ((u =? v) ∷ _A.ty).unify
      restUnifier <- unifier match {
        case UPositive(context, unifyingSubst, restoringSubst) => withCtx(context) {
          for {
            _Δmod <- _Δ.subst(unifyingSubst).toWhnfs
            t <- ((u̅.map(_.subst(unifyingSubst)) =? v̅.map(_.subst(unifyingSubst))) ∷ _Δmod).unify
          } yield t
        }
        case r => Right(r)
      }
    } yield unifier ∘ restUnifier
  }
}

/** Rearranges the given context while preserving type dependencies. After the
  * process, all types that don't directly or transitively depend on x are moved
  * before x. The rearrangement is returned as a permutation.
  *
  * The returned permutation maps each original binding index to the permuted
  * index.
  */
private def rearrange(x: Int)(using Γ: Context) : Seq[Int] = {
  val (_Θ, _A, _Δ) = Γ.splitAt(x)
  // all indices of bindings depending on x, including x
  val pivotSet = HashSet(x.deBruijnNumber)
  // indices of bindings that does not depend on x
  val before = ArrayBuffer[Int]()
  // indices of bindings that depends on x
  val after = ArrayBuffer[Int]()
  var ctx = _Θ + _A
  for ((b, i) <- _Δ.view.zipWithIndex) {
    val from = x - 1 - i
    withCtx(ctx) {
      val freeNumbers = b.ty.freeVars.map(_.deBruijnNumber)
      if (freeNumbers.intersect(pivotSet).isEmpty) {
        before += from
      } else {
        after += from
        pivotSet.addAll(freeNumbers)
      }
    }
    ctx += b
  }
  val permutation = new Array[Int](Γ.size)
  for(i <- 0 until after.size) {
    permutation(after(after.size - i - 1)) = i
  }
  permutation(x) = after.size
  for(i <- 0 until before.size) {
    permutation(before(before.size - i - 1)) = i + 1 + after.size
  }
  for(i <- x + 1 until Γ.size) {
    permutation(i) = i
  }
  ArraySeq.unsafeWrapArray(permutation)
}

// Permutation: index: position in Γ, value: position in resulting context
// The index starts from the right side, same as context.
private def shuffle(Γ: Context, permutation: Seq[Int]) : UPositive = {
  val size = Γ.size
  val σArray = new Array[Pattern](permutation.length)
  val τArray = new Array[Pattern](permutation.length)
  val ΓmodArray = new Array[(Binding[Type], Int)](permutation.length)
  for(case ((to, binding), from) <- permutation.zip(Γ.toList).zipWithIndex) {
    ΓmodArray(to) = (binding, from)
    σArray(from) = Pattern.PVar(to)(binding.name)
    assert(τArray(to).asInstanceOf[Any] == null)
    τArray(to) = Pattern.PVar(from)(binding.name)
  }
  val σ = Substitution(size, size, σArray.toIndexedSeq)
  val τ = Substitution(size, size, τArray.toIndexedSeq)
  val Γmod = Context.from(ArraySeq.unsafeWrapArray(ΓmodArray).zipWithIndex.map[Binding[Type]]{ case ((b, from), to) => 
      b.map(t => t.subst(σ.strengthen(from + 1)).asWhnf.raise(-(to + 1)))
  })
  new UPositive(Γmod, σ, τ) 
}

private def (t: Term) asWhnf : Whnf = t.match {
  case TWhnf(w) => w
  case _ => throw IllegalArgumentException()
}

private def isCyclic(x: Term, y: Term)(using Γ: Context)(using Σ: Signature) : Boolean = (x, y) match {
  case (x, TWhnf(WCon(_, ys))) => ys.exists(isAsRigidOrCyclic(x, _))
  case (x, TWhnf(WData(_, ys))) => ys.exists(isAsRigidOrCyclic(x, _))
  case (x, TWhnf(WRecord(_, ys))) => ys.exists(isAsRigidOrCyclic(x, _))
  case (x, TWhnf(WId(_, ty, u, v))) => isAsRigidOrCyclic(x, ty) || isAsRigidOrCyclic(x, u) || isAsRigidOrCyclic(x, v)
  case _ => false
}

private def isAsRigidOrCyclic(x: Term, y: Term)(using Γ: Context)(using Σ: Signature) : Boolean = 
  x == y || 
  ((x, y) match {
    case (TWhnf(WVar(x, xArgs)), TWhnf(WVar(y, yArgs))) =>
      x == y && 
      xArgs.size >= yArgs.size &&
      xArgs.take(yArgs.size).map(simplElim) == yArgs.map(simplElim)
    case _ => false
  }) ||
  isCyclic(x, y)

private def idTypes(Δ: Telescope, u̅: List[Term], v̅: List[Term]) : List[Binding[Type]] = (Δ, u̅, v̅) match {
  case (Nil, Nil, Nil) => Nil
  case (_A :: Δ, u :: u̅, v :: v̅) => 
    s"e${_A.name}" ∷ WId(
      // Level does not matter here since the generated Id type is only used inside the unification
      // algorithm. The output of the unification algorithm never includes these generated Id types.
      TWhnf(lconst(0)), TWhnf(_A.ty), u, v) :: idTypes(Δ, u̅, v̅)
  case _ => throw IllegalArgumentException()
}

private def idType(_A: Type, u: Term, v: Term) : Binding[Type] = 
  // For the same reason above, the level of ID type does not matter.
  "e" ∷ WId(TWhnf(lconst(0)), TWhnf(_A), u, v)

private def simplTerm(tm: Term)(using Γ: Context)(using Σ: Signature) : Term = tm.toWhnf match {
  case Right(WFunction(a, b)) => TWhnf(WFunction(a.map(simplTerm), simplTerm(b)))
  case Right(w: Whnf) => TWhnf(w)
  case _ => tm
}

private def simplElim(el: Elimination)(using Γ: Context)(using Σ: Signature) : Elimination = el match {
  case Elimination.ETerm(t) => Elimination.ETerm(simplTerm(t))
  case Elimination.EProj(p) => el
}

private def positive(solutionCtx: Context, unifyingSubstFn: (ctx: Context) ?=> Substitution[Pattern], sourceCtx: Context, restoringSubstFn: (ctx: Context) ?=> Substitution[Pattern]) : UResult = {
  val unifyingSubst = unifyingSubstFn(using solutionCtx)
  val restoringSubst = restoringSubstFn(using sourceCtx)
  assert(unifyingSubst.targetContextSize == sourceCtx.size && 
      restoringSubst.targetContextSize == solutionCtx.size && 
      unifyingSubst.sourceContextSize == solutionCtx.size && 
      restoringSubst.sourceContextSize == sourceCtx.size)
  UPositive(solutionCtx, unifyingSubst, restoringSubst)
}

private given uSuccessToEither as Conversion[UResult, Result[UResult]] = Right(_)

private def failure(p: =?[Term] ∷ Type) : Result[UResult] = p match {
  case (u =? v) ∷ _A => Right(UInconclusive(_A, u, v))
}

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

private type DeBruijnNumber = Int

extension deBruijnIndexOps on (idx: Int) {
  def deBruijnNumber(using ctx: Context) : DeBruijnNumber = ctx.size - 1 - idx
}