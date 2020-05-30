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

class CoreSpec extends UnitSpec {
  val ns = InMemoryNamespace.createWithBuiltins("stalker.unit-test")
  given Namespace = ns
  val Σ = SignatureBuilder.create
  given Signature = Σ

  def (ft: FTerm) tt : Term = ft.toTt match {
    case Right(t) => t
    case Left(e) => fail(e.toString)
  }

  def (t: Term) fe : FTerm = t.toFe

  def haveType(_A: Term)(using Γ: Context) = Matcher { (x: Term) =>
    _A.whnf.flatMap(wA => new ∷(x, wA).check) match {
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

  inline def (tm: Term) ∷ (ty: Term)(using Γ: Context) = tm should haveType(ty)
}