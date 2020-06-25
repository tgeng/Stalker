import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.parser
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.stalker.common.Namespace
import io.github.tgeng.stalker.common.MutableNamespace
import io.github.tgeng.common._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}
import io.github.tgeng.common.Block._
import scala.languageFeature.existentials
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}
import io.github.tgeng.stalker.common.nsElemMutableSetOps

object Main {

  def main(args: Array[String]): Unit = {
    val termP = whitespaces >> parser.term << whitespaces

    val ns = MutableNamespace()
    ns("FooBar").addQn("foo.bar.FooBar")
    println(ns.render("foo.bar.FooBar"))
    println(ns.render("one.two.three"))
  }
}
