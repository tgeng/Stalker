package io.github.tgeng.common

object debug {

  inline def [T] (inline t: T) printMe (prefix: String): T = {
    println(prefix + t)
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

  inline def [T](t: T) run (action: T => Unit) : T = {
    action(t)
    t
  }
}
