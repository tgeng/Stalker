import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.parser
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.InMemoryNamespace
import io.github.tgeng.stalker.core.common.LeafNamespace
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}
import io.github.tgeng.common.Block._
import scala.languageFeature.existentials
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}

object Main {

  def main(args: Array[String]): Unit = {

    // val sig = SignatureBuilder.create
    
    val termP = whitespaces >> parser.term << whitespaces

    println("=====")
    println(termP.parse("(t : Type -> String) -> String").getOrElse(???))
    println("=====")
    println(termP.parse("""
    |(f : (n : Nat) -> (A : Type 0lv) -> String -> Vector n A) -> (n : Nat) -> (A : Type zero) -> Vector n A
    """.stripMargin).getOrElse(???))
    println("=====")
    println(termP.parse("""
    con1{ 0lv, (n : Nat) -> Vector n String}
    """).getOrElse(???))
  }
}
