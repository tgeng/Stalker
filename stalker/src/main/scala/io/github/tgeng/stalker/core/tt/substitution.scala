package io.github.tgeng.stalker.core.tt

import io.github.tgeng.common.extraIntOps

trait Raisable[R] {
  def (r: R) raise(amount: Int) : R = r.raiseImpl(using RaiseSpec(0, amount))
  def (r: R) raiseImpl(using spec: RaiseSpec) : R
}

trait Substitutable[F, T: Raisable, R] {
  def (f: F) subst(s: Substitution[T]) : R = f.substituteImpl(using SubstituteSpec(0, s))
  def (f: F) substHead(tSub: T)(using ctx: Context) : R = f.substituteImpl(using SubstituteSpec(0, Substitution(ctx.size, ctx.size + 1, IndexedSeq(tSub))))
  def (f: F) substHead(tsSub: Seq[T])(using ctx: Context) : R = f.substituteImpl(using SubstituteSpec(0, Substitution(ctx.size, ctx.size + tsSub.size, tsSub.toIndexedSeq.reverse)))
  def (f: F) substituteImpl(using spec: SubstituteSpec[T]) : R
}

/** First element on the right. */
case class Substitution[T : Raisable] (sourceContextSize: Int, targetContextSize: Int, content : IndexedSeq[T]) {
  assert(targetContextSize >= content.size)
  def applyIndex(varFn: Int => T)(idx: Int) : T = {
    assert(idx >= 0 && idx < targetContextSize)
    if (idx < content.size) content(idx)
    else varFn(idx)
  }
  def map[R : Raisable](fn: T => R) : Substitution[R] = Substitution(sourceContextSize, targetContextSize, content.map(fn))
  def shiftAmount: Int = sourceContextSize - targetContextSize
  def unionSum(varFn : Int => T)(other: Substitution[T]) : Substitution[T] = {
    assert (other.sourceContextSize == sourceContextSize)
    Substitution(
      sourceContextSize, 
      targetContextSize + other.targetContextSize,
      other.materialize(varFn).content ++ content) 
  }

  def materialize(varFn: Int => T): Substitution[T] = Substitution(
    sourceContextSize, 
    targetContextSize, 
    content ++ ((sourceContextSize - (targetContextSize - content.size)) until sourceContextSize).map(varFn))

  def extendBy(varFn : Int => T)(Δ: Telescope) = {
    val size = Δ.size
    Substitution(
      sourceContextSize + size, 
      targetContextSize + size, 
      content.map(_.raise(size)).prependedAll((0 until size).map(varFn)))
  }

  def drop(count: Int) = Substitution(sourceContextSize, targetContextSize - count, content.drop(count))

  def keep(count: Int) = drop(targetContextSize - count)

  def delete(varFn: Int => T)(idx: Int) : Substitution[T] = {
    val materialized = materialize(varFn)
    Substitution(sourceContextSize, targetContextSize - 1, materialized.content.patch(idx, IndexedSeq.empty, 1))
  }

  /** Extend the source context with additional bindings. */
  def weaken(count: Int) = Substitution(sourceContextSize + count, targetContextSize, content.map(_.raise(count)))

  /** Drop unused tail bindings from the  source context. */
  def strengthen(count: Int) = {
    assert(targetContextSize - content.size <= sourceContextSize - count)
    Substitution(sourceContextSize - count, targetContextSize, content.map(_.raise(-count)))
  }
}

type ComposableSubstitutable[T] = Substitutable[T, T, T]

extension substitutionCompositionOps on [T : ComposableSubstitutable : Raisable](s: Substitution[T]) {
  def comp(varFn : Int => T)(r: Substitution[T]) : Substitution[T] = {
    assert (s.sourceContextSize == r.targetContextSize)
    Substitution[T](r.sourceContextSize, s.targetContextSize, s.materialize(varFn).content.map(_.subst(r)))
  }
}

object Substitution {
  def id[T : Raisable](using Γ: Context) : Substitution[T] = Substitution(Γ.size, Γ.size, IndexedSeq.empty)

  def none[T : Raisable](using Γ: Context) : Substitution[T] = Substitution(Γ.size, 0, IndexedSeq.empty)

  def of[T : Raisable](t: T)(using Γ: Context) : Substitution[T] = Substitution(Γ.size, 1, IndexedSeq(t))

  def from[T : Raisable](m: Map[Int, T])(using Γ: Context) : Substitution[T] = {
    val content = m.toSeq.sortBy((k, v) => k).zipWithIndex.map{case ((k, v), i) => 
      if (k != i) throw IllegalStateException()
      v
    }.toIndexedSeq
    Substitution(Γ.size, content.size, content)
  }
  
}

extension patternSubstitutionOps on (s: Substitution[Pattern]) {
  def apply = s.applyIndex(i => Pattern.PVar(i)("_" + i.sub))
  def \ = s.delete(i => Pattern.PVar(i)("_" + i.sub))
  def ⊎(other: Substitution[Pattern]) = s.unionSum(i => Pattern.PVar(i)("_" + i.sub))(other)
  def ⊎(p: Pattern) : Substitution[Pattern] = s ⊎ Substitution(s.sourceContextSize, 1, IndexedSeq(p))
  def ⊎(ps: Seq[Pattern]) : Substitution[Pattern] = s ⊎ Substitution(s.sourceContextSize, 1, ps.toIndexedSeq.reverse)
  def extendBy(Δ: Telescope) = s.extendBy(i => Pattern.PVar(i)("_" + i.sub))(Δ)
  def ∘(other: Substitution[Pattern]) : Substitution[Pattern] = s.comp(i => Pattern.PVar(i)("_" + i.sub))(other)
}

extension termSubstitutionOps on (s: Substitution[Term]) {
  def apply = s.applyIndex(i => Term.TWhnf(Whnf.WVar(i, Nil)))
  def \ = s.delete(i => Term.TWhnf(Whnf.WVar(i, Nil)))
  def ⊎(other: Substitution[Term]) = s.unionSum(i => Term.TWhnf(Whnf.WVar(i, Nil)))(other)
  def ⊎(t: Term) : Substitution[Term] = s ⊎ Substitution(s.sourceContextSize, 1, IndexedSeq(t))
  def ⊎(ts: Seq[Term]) : Substitution[Term] = s ⊎ Substitution(s.sourceContextSize, 1, ts.toIndexedSeq.reverse)
  def extendBy(Δ: Telescope) = s.extendBy(i => Term.TWhnf(Whnf.WVar(i, Nil)))(Δ)
  def ∘(other: Substitution[Term]) : Substitution[Term] = s.comp(i => Term.TWhnf(Whnf.WVar(i, Nil)))(other)
}

case class RaiseSpec(private val bar:Int, private val amount:Int) {
  def raised : RaiseSpec = RaiseSpec(bar + 1, amount)
  def trans(idx: Int) : Int = if(idx >= bar) idx + amount else idx
}

case class SubstituteSpec[T : Raisable](private val offset: Int, private val substitution: Substitution[T]) {
  def raised : SubstituteSpec[T] = SubstituteSpec(offset + 1, substitution.map(t => t.raise(1)))
  def trans(idx: Int) : Either[Int, T] = 
    if (idx >= offset) {
      val idxMod = idx - offset
      assert (idxMod >= 0 && idxMod < substitution.targetContextSize)
      if (idxMod < substitution.content.size) {
        Right(substitution.content(idx - offset)) 
      } else {
        Left(idx + substitution.shiftAmount)
      }
    }
    else {
        Left(idx)
    }
  def map[R : Raisable](fn: T => R) : SubstituteSpec[R] = SubstituteSpec(offset, substitution.map(fn))
}

object substitutionConversion {
  given patternSubstToTermSubst as Conversion[Substitution[Pattern], Substitution[Term]] = _.map(_.toTerm)
  given patternSubstToTermSubstSpec as Conversion[SubstituteSpec[Pattern], SubstituteSpec[Term]] = _.map(_.toTerm)
}