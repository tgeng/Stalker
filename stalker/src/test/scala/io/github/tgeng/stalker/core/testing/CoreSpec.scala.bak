package io.github.tgeng.stalker.core.testing

import scala.language.implicitConversions
import org.scalatest.matchers._
import org.scalatest.Matchers
import io.github.tgeng.testing.UnitSpec
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.Namespace
import io.github.tgeng.stalker.core.common.LocalNames
import io.github.tgeng.stalker.core.tt.MutableNamespace
import io.github.tgeng.parse._
import io.github.tgeng.parse.string._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.fe.pprint._
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.tt.typingRelation
import io.github.tgeng.stalker.core.tt.reduction.toWhnf
import io.github.tgeng.stalker.core.tt.typing._
import io.github.tgeng.testing.UnitSpec

import matchers._
import Term._

class CoreSpec extends UnitSpec with Helpers {
  val ns = MutableNamespace.createWithBuiltins("stalker.unit-test")
  given MutableNamespace = ns
  val Σ = FSignatureBuilder.create
  given Signature = Σ
  given Context = Context.empty
  given LocalIndices = LocalIndices()
  given LocalNames = LocalNames()

  inline def (tm: Term) ∷ (ty: Term)(using LocalNames, Context) = tm should haveType(ty)
  inline def (tm: Term) !∷ (ty: Term)(using LocalNames, Context) = tm shouldNot haveType(ty)

  inline def (tm: Term) ~> (w: FTerm)(using LocalIndices, LocalNames, Context) = tm should haveWhnf(w)
  inline def (tm: Term) !~> (w: FTerm)(using LocalIndices, LocalNames, Context) = tm shouldNot haveWhnf(w)

  def (x: Term) ≡ (y: Term) = (new ≡(x, y), true)
  def (x: Term) ≢ (y: Term) = (new ≡(x, y), false)

  inline def (e: (≡[Term], Boolean)) ∷ (ty: Term)(using LocalIndices, LocalNames, Context) = e match {
    case (e, true) => e should holdUnderType(ty)
    case (e, false) => e shouldNot holdUnderType(ty)
  }

  inline def (l1: Term) <= (l2: Term)(using LocalIndices, LocalNames, Context) = l1 should beALowerOrEqualLevelThan(l2)
  
  inline def (sb: FSignatureBuilder) +=! (d: FDeclaration)(using LocalIndices, LocalNames, Context) = {
    sb += d match {
      case Right(()) => ()
      case Left(e) => throw Exception(pp"$e", e.trace)
    }
  }
}