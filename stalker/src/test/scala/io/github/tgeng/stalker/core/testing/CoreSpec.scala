package io.github.tgeng.stalker.core.testing

import scala.language.implicitConversions
import io.github.tgeng.stalker.testing.UnitSpec
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.InMemoryNamespace
import io.github.tgeng.parse._
import io.github.tgeng.parse.string._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.testing.UnitSpec

class CoreSpec extends UnitSpec {
  val namespace = InMemoryNamespace.createWithBuiltins("stalker.unit-test")
  given Namespace = namespace

  def (ft: FTerm) tt : Term = ft.toTt match {
    case Right(t) => t
    case Left(e) => fail(e.toString)
  }

  def (t: Term) fe : FTerm = t.toFe
}