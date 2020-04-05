package io.github.tgeng.stalker.testing

import scala.language.implicitConversions
import org.scalatest.matchers._
import org.scalatest.Matchers
import io.github.tgeng.stalker.core._
import io.github.tgeng.stalker.core.typing._
import io.github.tgeng.stalker.core.typing.checkTerm
import io.github.tgeng.stalker.core.typingRelation

trait TypingMatchers {
  def haveType(_A: Term)(using Γ: Telescope)(using Σ: Signature) = Matcher { (x: Term) =>
    MatchResult(
      _A.whnf.flatMap(wA => (x ∷ wA).check(using Γ)(using Σ))isRight,
      s"Term $x did not have type $_A",
      s"Term $x had type $_A")
  }

  def haveLevel(l: Int)(using Γ: Telescope)(using Σ: Signature) = Matcher { (x: Term) =>
    MatchResult(
      x.whnf.flatMap(_.level) match {
        case Right(actualLevel) => actualLevel == l
        case _ => false
      },
      s"Type $x was not at level $l",
      s"Type $x was at level $l",
    )
  }
}