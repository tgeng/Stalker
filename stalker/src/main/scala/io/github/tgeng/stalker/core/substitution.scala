package io.github.tgeng.stalker.core

trait Raisable[R] {
  def raise(amount: Int) : R = raiseImpl(using RaiseSpec(0, amount))
  def raiseImpl(using spec: RaiseSpec) : R
}

trait Substitutable[T <: Raisable[T], R] {
  def subst(s: Substitution[T]) : R = substituteImpl(using SubstituteSpec(0, s))
  def substituteImpl(using spec: SubstituteSpec[T]) : R
}

/** First element on the right. */
case class Substitution[T <: Raisable[T]] (sourceContextSize: Int, content : IndexedSeq[T]) {
  def get(idx: Int) = content(idx)
  def map[R <: Raisable[R]](fn: T => R) : Substitution[R] = Substitution(sourceContextSize, content.map(fn))
  def shiftAmount: Int = sourceContextSize - content.size
  def ⊎(other: Substitution[T]) : Substitution[T] = {
    if (other.sourceContextSize != sourceContextSize) throw IllegalArgumentException("Mismatched source context")
    Substitution(sourceContextSize, other.content ++ content) 
  }
  def extendBy(size: Int) = Substitution(sourceContextSize + size, content.map(_.raise(size)))
}

extension substitutionCompositionOps on [T <: Substitutable[T, T] with Raisable[T]](s: Substitution[T]) {
  def ∘ (r: Substitution[T]) : Substitution[T] = {
    if (s.sourceContextSize != r.content.size) {
      throw IllegalArgumentException("Mismatched substitutions for composition")
    }
    Substitution[T](r.sourceContextSize, s.content.map(_.subst(r)))
  }
}

case class RaiseSpec(private val bar:Int, private val amount:Int) {
  def raised : RaiseSpec = RaiseSpec(bar + 1, amount)
  def trans(idx: Int) : Int = if(idx >= bar) idx + amount else idx
}

case class SubstituteSpec[T <: Raisable[T]](private val offset: Int, private val substitution: Substitution[T]) {
  def raised : SubstituteSpec[T] = SubstituteSpec(offset + 1, substitution.map(t => t.raise(1)))
  def trans(idx: Int) : Either[Int, T] = 
    if (idx >= offset) Right(substitution.get(idx - offset)) 
    else Left(idx - substitution.content.size + substitution.sourceContextSize)
  def map[R <: Raisable[R]](fn: T => R) : SubstituteSpec[R] = SubstituteSpec(offset, substitution.map(fn))
}

object substitutionConversion {
  given termToSubstitution(using Γ: Context) as Conversion[Term, Substitution[Term]] = t =>  Substitution(Γ.size, IndexedSeq(t))
  given termsToSubstitution(using Γ: Context) as Conversion[Seq[Term], Substitution[Term]] = ts =>  Substitution(Γ.size, ts.toIndexedSeq.reverse)
  given patternToSubstitution(using Γ: Context) as Conversion[Pattern, Substitution[Pattern]] = t =>  Substitution(Γ.size, IndexedSeq(t))
  given patternsToSubstitution(using Γ: Context) as Conversion[Seq[Pattern], Substitution[Pattern]] = ts =>  Substitution(Γ.size, ts.toIndexedSeq.reverse)
  given patternSubstToTermSubst as Conversion[Substitution[Pattern], Substitution[Term]] = _.map(_.toTerm)
  given patternSubstToTermSubstSpec as Conversion[SubstituteSpec[Pattern], SubstituteSpec[Term]] = _.map(_.toTerm)
}