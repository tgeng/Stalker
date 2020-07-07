package io.github.tgeng.stalker.core.testing

import scala.language.implicitConversions
import org.scalatest.matchers._
import org.scalatest.Matchers

import io.github.tgeng.common.eitherOps
import io.github.tgeng.common.optionOps
import io.github.tgeng.parse._
import io.github.tgeng.parse.string._
import io.github.tgeng.testing.UnitSpec
import io.github.tgeng.stalker
import stalker.core
import stalker.common._
import core.tt._
import core.fe._
import core.fe.builders._
import core.fe.pprint._
import core.io._

import matchers._
import Term._

class CoreSpec extends UnitSpec with Helpers {
  given LocalFtCtx = LocalFtCtx()
  given LocalTfCtx = LocalTfCtx()
  given Context = Context.empty

  inline def (tm: Term) ∷ (ty: Term)(using LocalTfCtx, Context, Signature, Namespace) = tm should haveType(ty)
  inline def (tm: Term) !∷ (ty: Term)(using LocalTfCtx, Context, Signature, Namespace) = tm shouldNot haveType(ty)

  inline def (tm: Term) ~> (w: FTerm)(using LocalFtCtx, LocalTfCtx, Context, Signature, Namespace) = tm should haveWhnf(w)
  inline def (tm: Term) !~> (w: FTerm)(using LocalFtCtx, LocalTfCtx, Context, Signature, Namespace) = tm shouldNot haveWhnf(w)

  def (x: Term) ≡ (y: Term) = (new ≡(x, y), true)
  def (x: Term) ≢ (y: Term) = (new ≡(x, y), false)

  inline def (e: (≡[Term], Boolean)) ∷ (ty: Term)(using LocalFtCtx, LocalTfCtx, Context, Signature, Namespace) = e match {
    case (e, true) => e should holdUnderType(ty)
    case (e, false) => e shouldNot holdUnderType(ty)
  }

  inline def (l1: Term) <= (l2: Term)(using LocalFtCtx, LocalTfCtx, Context, Signature, Namespace) = l1 should beALowerOrEqualLevelThan(l2)

  val pathResolver = PathResolver.createTmp()
  val moduleLoader = ModuleLoader(pathResolver)
  val rootNamespaceLoader = RootNamespaceLoader(moduleLoader)
  val mutualGroupLoader = MutualGroupLoader(rootNamespaceLoader)
  val signatureLoader = SignatureLoader(mutualGroupLoader)

  def withSignature(qn: QualifiedName)(action: (Signature, Namespace)?=> Unit) = {
    val namespace = rootNamespaceLoader.loadNamespace(qn, qn) match {
      case Right(Some(ns)) => ns
      case Right(None) => throw Exception(s"Cannot find namespace at $qn.")
      case Left(e) => throw Exception(s"Failed to resolve namespace at $qn. Error: $e", e.trace)
    }
    given Namespace = namespace
    val signature = signatureLoader.loadSignature(qn) match {
      case Right(sig) => sig
      case Left(e) => throw Exception(pp"Failed to load signature at $qn. Error: $e", e.trace)
    }
    action(using signature, namespace)
  }
}