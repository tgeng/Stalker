package io.github.tgeng.stalker.core.tt

import scala.collection.Seq
import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.common.LocalNames

import Term._
import Whnf._
import Elimination._

object utils {
  def (self: Term) app(t: Term)(using ctx: Context): Result[Term] = self.app(Elimination.ETerm(t))
  def (self: Term) app(f: String)(using ctx: Context): Result[Term] = self.app(Elimination.EProj(f))
  
  def (self: Term) app(e: Elimination)(using ctx: Context) : Result[Term] = self match {
    case TRedux(fn, elims) => Right(TRedux(fn, elims :+ e))
    case TWhnf(Whnf.WVar(idx, elims)) => Right(TWhnf(Whnf.WVar(idx, elims :+ e)))
    case _ => typingErrorWithCtx(s"Cannot apply $e to $this.")
  }
  
  def (self: Term)app(e̅: Seq[Elimination])(using ctx: Context) : Result[Term] = e̅.foldLeft[Result[Term]](Right(self))((acc, e) => acc.flatMap(_.app(e)))
  
  def typingErrorWithCtx(msg: Seq[Any])(using ctx: Context) = typingErrorWithNames(msg)(using ctx.toLocalNames)
}
