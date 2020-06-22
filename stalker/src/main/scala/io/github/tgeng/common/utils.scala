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

  def findFirstEitherOption(f: R1 => Either[L, Option[R2]]) : Either[L, Option[R2]] = {
    for (e <- self) {
      f(e) match {
        case Right(Some(r2))  => return Right(Some(r2))
        case Right(None) => ()
        case Left(e) => return Left(e)
      }
    }
    Right(None)
  }

  def findFirstOption(f: R1 => Option[R2]) : Option[R2] = {
    for (e <- self) {
      f(e) match {
        case Some(r2)  => return Some(r2)
        case _ => ()
      }
    }
    None
  }
}

extension extraSeqOps on [L, R1, R2, CC[_], C <: SeqOps[R1, CC, C]] (self: C) {
  def liftMap(f: R1 => Either[L, R2]) : Either[L, CC[R2]] = 
    self.foldLeft[Either[L, CC[R2]]](Right(self.empty.asInstanceOf[CC[R2]]))((acc, e) => acc.flatMap(acc => f(e)
    .map(e => (acc.asInstanceOf[SeqOps[R2, CC, C]] :+ e).asInstanceOf[CC[R2]])))

  def liftOptionMap(f: R1 => Option[R2]) : Option[CC[R2]] = 
    self.foldLeft[Option[CC[R2]]](Some(self.empty.asInstanceOf[CC[R2]]))((acc, e) => acc.flatMap(acc => f(e)
    .map(e => (acc.asInstanceOf[SeqOps[R2, CC, C]] :+ e).asInstanceOf[CC[R2]])))
}

extension extraSetOps on [L, R1, R2, CC[_], C <: SetOps[R1, CC, C]] (self: C) {
  def liftMap(f: R1 => Either[L, R2]) : Either[L, CC[R2]] = 
    self.foldLeft[Either[L, CC[R2]]](Right(self.empty.asInstanceOf[CC[R2]]))((acc, e) => acc.flatMap(acc => f(e)
    .map(e => (acc.asInstanceOf[SetOps[R2, CC, Nothing]] union Set(e)).asInstanceOf[CC[R2]])))

  def liftOptionMap(f: R1 => Option[R2]) : Option[CC[R2]] = 
    self.foldLeft[Option[CC[R2]]](Some(self.empty.asInstanceOf[CC[R2]]))((acc, e) => acc.flatMap(acc => f(e)
    .map(e => (acc.asInstanceOf[SetOps[R2, CC, Nothing]] union Set(e)).asInstanceOf[CC[R2]])))
}

extension nullOps on [T, R](t: T | Null) {
  inline def !! = t.asInstanceOf[T]
  inline def ifNullUse (default: T) : T = if (t == null) default else t
  inline def ifNotNull(fn: T => R) : R | Null = if (t == null) null else fn(t)
}

extension eitherOps on [L, R](e: Either[L, R]) {
  def !!! : R = e match {
    case Right(r) => r
    case Left(l) => throw IllegalArgumentException(s"Expected $e to be a right value.")
  }
}

extension optionOps on [T](e: Option[T]) {
  def !!! : T = e match {
    case Some(t) => t
    case None => throw IllegalArgumentException(s"Expected $e to be a present.")
  }
}