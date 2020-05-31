package io.github.tgeng.stalker.core.testing

import scala.language.implicitConversions
import org.scalatest.matchers._
import org.scalatest.Matchers
import io.github.tgeng.stalker.testing.UnitSpec
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.InMemoryNamespace
import io.github.tgeng.parse._
import io.github.tgeng.parse.string._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.fe.pprint._
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.tt.typingRelation
import io.github.tgeng.stalker.core.tt.typing.checkTerm
import io.github.tgeng.stalker.core.tt.reduction.whnf
import io.github.tgeng.stalker.testing.UnitSpec

import Term._

object matchers {
  def haveType(_A: Term)(using LocalNames, Context, Signature, Namespace) = Matcher { (x: Term) =>
    _A.whnf.flatMap(wA => (x ∷ wA).check) match {
      case Right(_) => MatchResult(
        true,
        "",
        pp"Term $x had type $_A")
      case Left(e) => MatchResult(
        false,
        pp"Term $x failed type checking against $_A because $e",
        ""
      )
    }
  }

  def haveWhnf(w: FTerm)(using LocalIndices, LocalNames, Context, Signature, Namespace) = Matcher { (t: Term) => 
    (for wt <- t.whnf
    yield MatchResult(
      TWhnf(wt).toFeImpl == w,
      pp"Term $t did not reduce to $w but to $wt.",
      pp"Term $t reduced to $w."
    )) match {
      case Right(m) => m
      case Left(e) => throw Exception(e.toBlock.toString)
    }
  }
}