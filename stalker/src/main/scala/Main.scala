import scala.language.implicitConversions
import io.github.tgeng.stalker.core.fe.parser
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.InMemoryNamespace
import io.github.tgeng.stalker.core.common.LeafNamespace
import io.github.tgeng.common._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}
import io.github.tgeng.common.Block._
import scala.languageFeature.existentials
import io.github.tgeng.stalker.core.fe.ftConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}

object Main {

  def main(args: Array[String]): Unit = {
    val termP = whitespaces >> parser.term << whitespaces
  }
}
