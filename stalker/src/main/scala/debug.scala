package debug

inline def [T](inline v: T) printMe : T = {
  println(exprName(v) + " = " + v)
  v
}

inline def [T] (inline msg: String) || (t: => T) : T = {
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
