package io.github.tgeng.stalker.core.testing

import scala.language.implicitConversions
import io.github.tgeng.stalker.testing.UnitSpec
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.InMemoryNamespace
import io.github.tgeng.parse._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.testing.UnitSpec

class CoreSpec extends UnitSpec {
  val namespace = InMemoryNamespace.createWithBuiltins("stalker.unit-test")
  given Namespace = namespace

  def fterm(s: String) : FTerm = (parser.term << eof).parse(s) match {
    case Right(t) => t
    case Left(e) => fail(e.toString)
  }

  def (ft: FTerm) tt : Term = ft.toTt match {
    case Right(t) => t
    case Left(e) => fail(e.toString)
  }

  def term(s: String) : Term = fterm(s).tt

  def openTerm(s: String)(using LocalIndices) : Term = fterm(s).toTtImpl match {
    case Right(t) => t
    case Left(e) => fail(e.toString)
  }
}