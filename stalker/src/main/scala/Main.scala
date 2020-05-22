import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.parser._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}
import io.github.tgeng.common.Block._
import scala.languageFeature.existentials

object Main {

  def main(args: Array[String]): Unit = {

    // val sig = SignatureBuilder.create
    
    // val ns = InMemoryNamespace()
    // ns("Vector") = Root/"stalker"/"collection"/"Vector"
    // ns("Nat") = Root/"stalker"/"collection"/"Nat"
    // ns("String") = Root/"stalker"/"collection"/"Nat"
    // ns("zero") = Root/"mymodule"/"zero"

    // given Namespace = ns

    // val termP = whitespaces >> term << whitespaces

    // println(termP.parse("(t : Type -> String) -> String"))
    // println(termP.parse("""
    // |(f : (n : Nat) -> (A : Type 0lv) -> String -> Vector n A) -> (n : Nat) -> (A : Type zero) -> Vector n A
    // """.stripMargin))
    // println("======")
    // println(termP.parse("""
    // con1{ 0lv, (n : Nat) -> Vector n String}
    // """))
    /*
      (f : A -> B -> C) ->
      D
     */

    val sb = StringBuilder()
    sb.append("    ")

    flow(
      "def",
      "foo", 
      "(", 
      chopDown(
        concat(oneLine("a", ":", "Int"), ","),
        concat(oneLine("b", ":", "Int"), ","),
        concat(oneLine("c", ":", "Int"), ","),
        oneLine("d", ":", "Int"),
      ),
      ")",
      "=",
      "{",
        exhibit(
          "statement 1",
          "statement 2",
          "statement 3",
        ),
      multiLine("}"),
    ).print(sb, 20)
    println(sb.toString)
  }
}
