package io.github.tgeng.testing

import scala.language.implicitConversions
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.EitherValues
import org.scalatest.Matchers

class UnitSpec extends AnyFreeSpec with Matchers {
  def [L, R](e: Either[L, R]) rightVal : R = e match {
    case Right(r) => r
    case _ => throw Exception(s"$e is not a right value.")
  }

  def [L, R](e: Either[L, R]) leftVal : L = e match {
    case Left(l) => l
    case _ => throw Exception(s"$e is not a left value.")
  }
}