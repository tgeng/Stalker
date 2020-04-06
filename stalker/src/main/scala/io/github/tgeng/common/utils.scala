package io.github.tgeng.common

import scala.collection.Seq
import scala.collection.SeqOps

extension extraSeqOps on [L, R1, R2, CC[_], C <: SeqOps[R1, CC, C]] (self: C) {
  def liftMap(f: R1 => Either[L, R2]) : Either[L, CC[R2]] = 
    self.foldRight[Either[L, CC[R2]]](Right(self.empty.asInstanceOf[CC[R2]]))((e, acc) => acc.flatMap(acc => f(e)
    .map(e => (e +: acc.asInstanceOf[SeqOps[R1, CC, C]]).asInstanceOf[CC[R2]])))

  def liftMap(f: R1 => Option[R2]) : Option[CC[R2]] = 
    self.foldRight[Option[CC[R2]]](Some(self.empty.asInstanceOf[CC[R2]]))((e, acc) => acc.flatMap(acc => f(e)
    .map(e => (e +: acc.asInstanceOf[SeqOps[R1, CC, C]]).asInstanceOf[CC[R2]])))
}