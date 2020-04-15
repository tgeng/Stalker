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
    Substitution(sourceContextSize + other.sourceContextSize, other.content ++ content.map(_.raise(other.sourceContextSize))) 
  }
}

extension substitutionCompositionOps on [T <: Substitutable[T, T]](s: Substitution[T]) {
  def ∘ (r: Substitution[T]) : Substitution[T] = Substitution[T](r.sourceContextSize, s.content.map(_.subst(r)))
}

object Substitution {
  def id(size: Int) : Substitution[Pattern] = Substitution(size, (0 until size).map(Pattern.PVar(_)))
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
  given termToSubstitution as Conversion[Term, Substitution[Term]] = t =>  Substitution(0, IndexedSeq(t))
  given termsToSubstitution as Conversion[Seq[Term], Substitution[Term]] = ts =>  Substitution(0, ts.toIndexedSeq.reverse)
  given patternSubstToTermSubst as Conversion[Substitution[Pattern], Substitution[Term]] = _.map(_.toTerm)
  given patternSubstToTermSubstSpec as Conversion[SubstituteSpec[Pattern], SubstituteSpec[Term]] = _.map(_.toTerm)
}