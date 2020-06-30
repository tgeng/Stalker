package io.github.tgeng.stalker.core.testing

import scala.language.implicitConversions
import org.scalatest.matchers._
import org.scalatest.Matchers
import io.github.tgeng.testing.UnitSpec
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.Namespace
import io.github.tgeng.stalker.common.LocalNames
import io.github.tgeng.parse._
import io.github.tgeng.parse.string._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.fe.builders._
import io.github.tgeng.stalker.core.fe.pprint._
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.tt.typingRelation
import io.github.tgeng.stalker.core.tt.typing._
import io.github.tgeng.stalker.core.tt.reduction.toWhnf
import io.github.tgeng.testing.UnitSpec

trait Helpers {
  def (ft: FTerm) tt (using LocalIndices, Namespace): Term = ft.toTt match {
    case Right(t) => t
    case Left(e) => throw Exception(e.toString)
  }

  def (t: Term) fe (using LocalNames, Namespace): FTerm = t.toFe

  def (t: Term) whnf (using LocalNames, Context, Namespace, Signature) = t.toWhnf match {
    case Right(w) => w
    case Left(e) => throw Exception(e.toBlock.toString)
  }
}