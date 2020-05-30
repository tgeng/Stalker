package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.pprint.toBlock
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

import parser._

object builders {
  inline def [T](ctx: StringContext) ft() : FTerm = ft(ctx.parts(0))

  inline def [T](ctx: StringContext) t()(using Namespace) : Term = t(ctx.parts(0))

  inline def [T](ctx: StringContext) ot(using LocalIndices)(using Namespace) : Term = ot(ctx.parts(0))

  def ft(s: String) : FTerm = {
    (whitespaces >> term << whitespaces << eof).parse(s) match {
      case Right(t) => t
      case Left(e) => throw Exception(e.toString)
    }
  }

  def t(s: String)(using Namespace) : Term = 
    ft(s).toTt match {
      case Right(t) => t
      case Left(e) => throw Exception(e.toBlock.toString)
    }

  def ot(s: String)(using LocalIndices)(using Namespace) : Term =
    ft(s).toTtImpl match {
      case Right(t) => t
      case Left(e) => throw Exception(e.toBlock.toString)
    }
}