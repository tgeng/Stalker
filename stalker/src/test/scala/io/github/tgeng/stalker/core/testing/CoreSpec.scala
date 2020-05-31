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

import matchers._
import Term._

class CoreSpec extends UnitSpec {
  val ns = InMemoryNamespace.createWithBuiltins("stalker.unit-test")
  given Namespace = ns
  val Σ = SignatureBuilder.create
  given Signature = Σ
  given Context = Context.empty
  given LocalIndices = LocalIndices()
  given LocalNames = LocalNames()

  def (ft: FTerm) tt (using ctx:LocalIndices)(using ns: Namespace): Term = ft.toTtImpl match {
    case Right(t) => t
    case Left(e) => fail(e.toString)
  }

  def (t: Term) fe (using localVars: LocalNames)(using ns: Namespace): FTerm = t.toFeImpl

  inline def (tm: Term) ∷ (ty: Term)(using LocalNames, Context) = tm should haveType(ty)
  inline def (tm: Term) !∷ (ty: Term)(using LocalNames, Context) = tm shouldNot haveType(ty)

  inline def (tm: Term) ~> (w: FTerm)(using LocalIndices, LocalNames, Context) = tm should haveWhnf(w)
  inline def (tm: Term) !~> (w: FTerm)(using LocalIndices, LocalNames, Context) = tm shouldNot haveWhnf(w)
}