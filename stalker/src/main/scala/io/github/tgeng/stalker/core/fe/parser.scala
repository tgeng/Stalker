package io.github.tgeng.stalker.core.fe

import scala.language.postfixOps
import scala.language.implicitConversions
import scala.collection.Map
import io.github.tgeng.common.extraSeqOps._
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

object parser {
  import FTerm._
  import FElimination._

  private val bodyInvalidChars = " \\r\\n\\t()\\[\\]{},."
  private val bodyPattern = s"[^${bodyInvalidChars}]"
  private val headPattern = s"""[^`'"0-9${bodyInvalidChars}]"""
  private val name = P { s"$headPattern$bodyPattern*".rp.satisfying(!Set("->", ":", "=", "_").contains(_)) }
  private val level = P { "[0-9]+".rp.map(s => Right(FTLevel(Integer.parseInt(s)))) << "lv" }

  private def con(using opt: ParsingOptions) : Parser[Result[FTerm]] = P {
    for {
      n <- name
      args <- '{' >> whitespaces >> (termImpl sepBy (whitespaces >> ',' << whitespaces)) << whitespaces << '}'
    } yield args.liftMap(t => t).map(args => FTCon(n, args.toList))
  }

  private def ref(using opt: ParsingOptions) : Parser[Result[FTerm]] = P {
    (name sepBy1 '.').map (names => names.toList match {
      case head :: names => Right(FTRedux(head, names, Nil))
      case _ => throw IllegalStateException("sepBy1 must return non empty vector")
    })
  }

  private def atom(using opt: ParsingOptions) : Parser[Result[FTerm]] = P {
    '('.! >> termImpl(using opt.copy(appDelimiter = whitespaces)) << ')' | con | ref | level
  }

  private def proj = '.'.! >> name

  private def elim(using opt: ParsingOptions) : Parser[Result[FElimination]] = P {
    atom.map(t => t.map(FETerm(_))) | proj.map(p => Right(FEProj(p)))
  }

  private def app(using opt: ParsingOptions) : Parser[Result[FTerm]] = P {
    lift(atom, (opt.appDelimiter >> elim).*).flatMap {
      case (Right(t), elims) => if (elims.isEmpty) {
        pure(Right(t))
      } else {
        val liftedElims : Result[Vector[FElimination]] = elims.liftMap(e => e)
        (t, liftedElims) match {
          case (FTRedux(head, name, es1), Right(es2)) => pure(Right(FTRedux(head, name, es1 ++ es2)))
          case (FTFunction(_, _), Right(_)) => pure(typingError("Cannot apply to function type."))
          case (_, Left(e)) => pure(Left(e))
          case _ => throw IllegalStateException()
        }
      }
      case (Left(e), _) => pure(Left(e))
    }
  }

  private def binding(using opt: ParsingOptions) : Parser[Result[FBinding]] = P {
    '(' >> whitespaces >> lift(name << whitespaces, ':'.! >> whitespaces >> termImpl).map((x, ty) => ty.map(FBinding(x, _))) << whitespaces << ')' | 
    app.map(_.map(t => FBinding("", t)))
  }

  private def termImpl(using opt: ParsingOptions) : Parser[Result[FTerm]] = P {
    for {
      bdn <- (binding << whitespaces << "->".! << whitespaces).?
      r <- bdn match {
        case Some(Right(b)) => for t <- termImpl(using opt) yield t.map(FTFunction(b, _))
        case Some(Left(e)) => pure(Left(e))
        case None => app
      }
    } yield r
  }

  def term = P { termImpl(using ParsingOptions()) }
}

private case class ParsingOptions(val appDelimiter: Parser[?] = spaces)
