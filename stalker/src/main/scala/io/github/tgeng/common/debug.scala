package io.github.tgeng.common

inline def [T] (inline t: T) printMe : T = {
  println(t)
  t
}

inline def [T] (inline msg: String) | (t: => T) : T = {
  println(msg)
  t
}

inline def exprName[T](inline t: T) : String = ${
  exprNameImpl('t) 
}
import scala.quoted._

private def exprNameImpl(t: Expr[Any])(using qctx: QuoteContext) : Expr[String] = {
  import qctx.tasty._
  Literal(Constant(t.show)).seal.asInstanceOf[Expr[String]]
}