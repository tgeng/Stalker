package io.github.tgeng.common

extension indexedSeqOps on [T](self: IndexedSeq[T]) {
  def lastN(idx: Int) = self(self.length - 1 - idx)
}