package io.github.tgeng.common

import scala.collection.IterableOps
import scala.collection.SeqOps
import scala.collection.SetOps

extension extraIterableOps on [L, R1, R2, CC[_], C <: IterableOps[R1, CC, C]] (self: C) {
  def allRight(f : R1 => Either[L, ?]) : Either[L, Unit] = self.foldLeft[Either[L, Unit]](Right(())) {(acc, e) =>
    for {
      _ <- acc
      _ <- f(e)
    } yield ()
  }
}

extension extraSeqOps on [L, R1, R2, CC[_], C <: SeqOps[R1, CC, C]] (self: C) {
  def liftMap(f: R1 => Either[L, R2]) : Either[L, CC[R2]] = 
    self.foldRight[Either[L, CC[R2]]](Right(self.empty.asInstanceOf[CC[R2]]))((e, acc) => acc.flatMap(acc => f(e)
    .map(e => (e +: acc.asInstanceOf[SeqOps[R2, CC, C]]).asInstanceOf[CC[R2]])))

  def liftOptionMap(f: R1 => Option[R2]) : Option[CC[R2]] = 
    self.foldRight[Option[CC[R2]]](Some(self.empty.asInstanceOf[CC[R2]]))((e, acc) => acc.flatMap(acc => f(e)
    .map(e => (e +: acc.asInstanceOf[SeqOps[R2, CC, C]]).asInstanceOf[CC[R2]])))
}

extension extraSetOps on [L, R1, R2, CC[_], C <: SetOps[R1, CC, C]] (self: C) {
  def liftMap(f: R1 => Either[L, R2]) : Either[L, CC[R2]] = 
    self.foldLeft[Either[L, CC[R2]]](Right(self.empty.asInstanceOf[CC[R2]]))((acc, e) => acc.flatMap(acc => f(e)
    .map(e => (acc.asInstanceOf[SetOps[R2, CC, Nothing]] union Set(e)).asInstanceOf[CC[R2]])))

  def liftOptionMap(f: R1 => Option[R2]) : Option[CC[R2]] = 
    self.foldLeft[Option[CC[R2]]](Some(self.empty.asInstanceOf[CC[R2]]))((acc, e) => acc.flatMap(acc => f(e)
    .map(e => (acc.asInstanceOf[SetOps[R2, CC, Nothing]] union Set(e)).asInstanceOf[CC[R2]])))
}