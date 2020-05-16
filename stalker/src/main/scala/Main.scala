import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.parser._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

object Main {

  def main(args: Array[String]): Unit = {
    val ns = MutableNamespace()
    ns("Vector") = Root/"stalker"/"collection"/"Vector"
    ns("zero") = Root/"mymodule"/"zero"

    given Namespace = ns

    val termP = whitespaces >> term << whitespaces

    println(termP.parse("""
     (f : (n : Nat) -> String -> Vector n String) -> (n : Nat) -> (A : Type zero) -> Vector n A
    """))
  }
}
