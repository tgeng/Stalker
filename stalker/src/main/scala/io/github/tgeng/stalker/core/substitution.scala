package io.github.tgeng.stalker.core

trait Raisable[R] {
  def raise(amount: Int) : R = raiseImpl(using RaiseSpec(0, amount))
  def raiseImpl(using spec: RaiseSpec) : R
}

trait Substitutable[T <: Raisable[T], R] {
  def subst(s: Substitution[T]) : R = substituteImpl(using SubstituteSpec(0, s))
  def substHead(t: T)(using ctx: Context) : R = substituteImpl(using SubstituteSpec(0, Substitution(ctx.size, ctx.size + 1, IndexedSeq(t))))
  def substHead(ts: Seq[T])(using ctx: Context) : R = substituteImpl(using SubstituteSpec(0, Substitution(ctx.size, ctx.size + ts.size, ts.toIndexedSeq.reverse)))
  def substituteImpl(using spec: SubstituteSpec[T]) : R
}

/** First element on the right. */
case class Substitution[T <: Raisable[T]] (sourceContextSize: Int, targetContextSize: Int, content : IndexedSeq[T]) {
  assert(targetContextSize >= content.size)
  def map[R <: Raisable[R]](fn: T => R) : Substitution[R] = Substitution(sourceContextSize, targetContextSize, content.map(fn))
  def shiftAmount: Int = sourceContextSize - targetContextSize
  def unionSum(varFn : Int => T)(other: Substitution[T]) : Substitution[T] = {
    assert (other.sourceContextSize == sourceContextSize)
    Substitution(sourceContextSize, targetContextSize + other.targetContextSize, other.content ++ 
      ((other.sourceContextSize - (other.targetContextSize - other.content.size)) until other.sourceContextSize).map(varFn) ++ 
      content) 
  }

  // def +(t: T) = Substitution(sourceContextSize, targetContextSize + 1, t +: content)
  // def ++(ts: Seq[T]) = Substitution(sourceContextSize, targetContextSize + ts.size, content.prependedAll(ts.reverse))

  def extendBy(varFn : Int => T)(Δ: Telescope) = {
    val size = Δ.size
    Substitution(
      sourceContextSize + size, 
      targetContextSize + size, 
      content.map(_.raise(size)).prependedAll((0 until size).map(varFn)))
  }
}

object Substitution {
  def drop[T <: Raisable[T]](count: Int)(using Γ: Context) : Substitution[T] = {
    assert(count < Γ.size)
    Substitution(Γ.size, Γ.size - count, IndexedSeq.empty)
  }

  def id[T <: Raisable[T]](using Γ: Context) : Substitution[T] = drop(0)

  def none[T <: Raisable[T]](using Γ: Context) : Substitution[T] = Substitution(Γ.size, 0, IndexedSeq.empty)

  def of[T <: Raisable[T]](t: T)(using Γ: Context) : Substitution[T] = Substitution(Γ.size, 1, IndexedSeq(t))
}

extension patternSubstitutionUnionSum on (s: Substitution[Pattern]) {
  def ⊎(other: Substitution[Pattern]) = s.unionSum(Pattern.PVar(_))(other)
  def ⊎(p: Pattern) : Substitution[Pattern] = s ⊎ Substitution(s.sourceContextSize, 1, IndexedSeq(p))
  def ⊎(ps: Seq[Pattern]) : Substitution[Pattern] = s ⊎ Substitution(s.sourceContextSize, 1, ps.toIndexedSeq.reverse)
  def extendBy(Δ: Telescope) = s.extendBy(Pattern.PVar(_))(Δ)
}

extension termSubstitutionUnionSum on (s: Substitution[Term]) {
  def ⊎(other: Substitution[Term]) = s.unionSum(i => Term.TWhnf(Whnf.WVar(i, Nil)))(other)
  def ⊎(t: Term) : Substitution[Term] = s ⊎ Substitution(s.sourceContextSize, 1, IndexedSeq(t))
  def ⊎(ts: Seq[Term]) : Substitution[Term] = s ⊎ Substitution(s.sourceContextSize, 1, ts.toIndexedSeq.reverse)
  def extendBy(Δ: Telescope) = s.extendBy(i => Term.TWhnf(Whnf.WVar(i, Nil)))(Δ)
}

extension substitutionCompositionOps on [T <: Substitutable[T, T] with Raisable[T]](s: Substitution[T]) {
  def ∘ (r: Substitution[T]) : Substitution[T] = {
    assert (s.sourceContextSize == r.targetContextSize)
    Substitution[T](r.sourceContextSize, s.targetContextSize, s.content.map(_.subst(r)))
  }
}

case class RaiseSpec(private val bar:Int, private val amount:Int) {
  def raised : RaiseSpec = RaiseSpec(bar + 1, amount)
  def trans(idx: Int) : Int = if(idx >= bar) idx + amount else idx
}

case class SubstituteSpec[T <: Raisable[T]](private val offset: Int, private val substitution: Substitution[T]) {
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
  def map[R <: Raisable[R]](fn: T => R) : SubstituteSpec[R] = SubstituteSpec(offset, substitution.map(fn))
}

object substitutionConversion {
  given patternSubstToTermSubst as Conversion[Substitution[Pattern], Substitution[Term]] = _.map(_.toTerm)
  given patternSubstToTermSubstSpec as Conversion[SubstituteSpec[Pattern], SubstituteSpec[Term]] = _.map(_.toTerm)
}