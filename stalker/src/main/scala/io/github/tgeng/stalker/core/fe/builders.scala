package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.pprint.toBlock
import io.github.tgeng.stalker.core.tt.contextOps
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.tt.typing.level
import io.github.tgeng.stalker.core.tt.reduction.toWhnf
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

import parser._

object builders {
  inline def [T](ctx: StringContext) ft() : FTerm = ft(ctx.parts(0))

  inline def [T](ctx: StringContext) t()(using LocalIndices, LocalNames)(using Namespace) : Term = t(ctx.parts(0))

  inline def [T](ctx: StringContext) b()(using LocalIndices, LocalNames, Context)(using Namespace, Signature) : Binding[Type] = b(ctx.parts(0))

  def ft(s: String) : FTerm = (whitespaces >> term << whitespaces << eof).parse(s) match {
    case Right(t) => t
    case Left(e) => throw Exception("Parsing FTerm failed:\n" + e.toStringWithInput(s))
  }

  def t(s: String)(using LocalIndices, LocalNames)(using Namespace) : Term = ft(s).toTt match {
    case Right(t) => t
    case Left(e) => throw Exception(e.toBlock.toString)
  }

  def b(s: String)(using LocalIndices, LocalNames, Context)(using Namespace, Signature) : Binding[Type] = {
    (whitespaces >> binding << whitespaces << eof).parse(s) match {
      case Right(b) => 
        (for b <- b.toTt
             _ <- b.ty.level
             _A <- b.ty.toWhnf
        yield Binding(_A)(b.name)) match {
          case Right(b) => b
          case Left(e) => throw Exception(e.toBlock.toString)
        }
      case Left(e) => throw Exception("Parsing binding failed:\n" + e.toStringWithInput(s))
    }
  }

  inline def [T](ctx: StringContext) q() : List[FCoPattern] = q(ctx.parts(0))

  def q(s: String) : List[FCoPattern] = (whitespaces >> coPatterns << whitespaces << eof).parse(s) match {
    case Right(q) => q
    case Left(e) => throw Exception("Parsing copatterns failed:\n" + e.toStringWithInput(s))
  }

  inline def [T](ctx: StringContext) decl() : FDeclaration = decl(ctx.parts(0).trim.asInstanceOf[String].stripMargin)

  def decl(s: String) : FDeclaration = (declaration ).parse(s) match {
    case Right(d) => d
    case Left(e) => throw Exception("Parsing declaration failed:\n" + e.toStringWithInput(s))
  }

  def withBindings[T](bindings: (LocalIndices, LocalNames, Context) ?=> (Namespace, Signature) ?=> Binding[Type]*)(action: (LocalIndices, LocalNames, Context) ?=> T)(using Namespace, Signature) : T = {
    val localIndices = LocalIndices()
    val localNames = LocalNames()
    var context = Context.empty
    for (b <- bindings) {
      val binding = b(using localIndices, localNames, context)
      localIndices.add(binding.name)
      localNames.add(binding.name)
      context += binding
    }
    action(using localIndices, localNames, context)
  }
}