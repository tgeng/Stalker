package io.github.tgeng.common

import scala.language.implicitConversions

object sugar {
  given eitherSugar[A, B] as Conversion[B, Either[A, B]] = (b: B) => Right(b)
  given eitherSugar[A, B, C](using bToC: Conversion[B, C]) as Conversion[B, Either[A, C]] = (b: B) => Right(bToC(b))
  given optionSugar[A] as Conversion[A, Option[A]] = (a: A) => Some(a)
  given optionSugar[A, B](using aToB: Conversion[A, B]) as Conversion[A, Option[B]] = (a: A) => Some(aToB(a))
}