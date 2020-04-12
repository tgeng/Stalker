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

object Substitution {
  def id[T <: Raisable[T]](size: Int, f: Int => T) : Substitution[T] = Substitution(size, (0 until size).map(f))
}

case class RaiseSpec(bar:Int, amount:Int)

case class SubstituteSpec[T <: Raisable[T]](offset: Int, substitution: Substitution[T]) {
  def raised : SubstituteSpec[T] = SubstituteSpec(offset + 1, substitution.map(t => t.raise(1)))
}

object substitutionConversion {
  given termToSubstitution as Conversion[Term, Substitution[Term]] = t =>  Substitution(0, IndexedSeq(t))
  given termsToSubstitution as Conversion[Seq[Term], Substitution[Term]] = ts =>  Substitution(0, ts.toIndexedSeq.reverse)
}