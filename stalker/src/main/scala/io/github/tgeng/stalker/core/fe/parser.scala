package io.github.tgeng.stalker.core.fe

import scala.language.postfixOps
import scala.language.implicitConversions
import scala.collection.Map
import io.github.tgeng.common.extraSeqOps._
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

object parser {
  import Term._
  import Elimination._
  import NamespaceElement._

  private val bodyInvalidChars = " \\r\\n\\t()\\[\\]{}."
  private val bodyPattern = s"[^${bodyInvalidChars}]"
  private val headPattern = s"""[^`'"0-9${bodyInvalidChars}]"""
  private val name = P { s"$headPattern$bodyPattern*".rp.satisfying(!Set("->", ":", "=", "_").contains(_)) }

  private def ref(using ns: Namespace)(using ln: LocalNames)(using opt: ParsingOptions) : Parser[Result[Term]] = P {
    for {
       n <- name
       r <- if (ln.contains(n)) {
         pure(Right(TVar(n, Nil)))
       } else ns.get(n) match {
          case Some(Sub(ns)) => ref(using ns)
          case Some(Leaf(qn)) => pure(Right(TRedux(qn, Nil)))
          case None => pure(noNameError(s"Unknown reference $n"))
       }
    } yield r
  }

  private def atom(using opt: ParsingOptions)(using ns: Namespace)(using ln: LocalNames) : Parser[Result[Term]] = P {
    '('.! >> termImpl(using opt.copy(appDelimiter = whitespace*)) << ')' | ref
  }

  private def proj = '.'.! >> name

  private def elim(using opt: ParsingOptions)(using ns: Namespace)(using ln: LocalNames) : Parser[Result[Elimination]] = P {
    atom.map(t => t.map(ETerm(_))) | proj.map(p => Right(EProj(p)))
  }

  private def app(using opt: ParsingOptions)(using ns: Namespace)(using ln: LocalNames) : Parser[Result[Term]] = P {
    lift(atom, (opt.appDelimiter >> elim).*).flatMap {
      case (Right(t), elims) => if (elims.isEmpty) {
        pure(Right(t))
      } else {
        val liftedElims : Result[Vector[Elimination]] = elims.liftMap(e => e)
        (t, liftedElims) match {
          case (TRedux(fn, es1), Right(es2)) => pure(Right(TRedux(fn, es1 ++ es2)))
          case (TVar(name, es1), Right(es2)) => pure(Right(TVar(name, es1 ++ es2)))
          case (TFunction(_, _), Right(_)) => pure(typingError("Cannot apply to function type."))
          case (_, Left(e)) => pure(Left(e))
          case _ => throw IllegalStateException()
        }
      }
      case (Left(e), _) => pure(Left(e))
    }
  }

  private def binding(using opt: ParsingOptions)(using ns: Namespace)(using ln: LocalNames) : Parser[Result[Binding]] = P {
    '(' >> lift(name << whitespaces, ':'.! >> whitespaces >> termImpl).map((x, ty) => ty.map(Binding(x, _))) << ')' | 
    app.map(_.map(t => Binding("", t)))
  }

  private def termImpl(using opt: ParsingOptions)(using ln: LocalNames)(using ns: Namespace) : Parser[Result[Term]] = P{
    for {
      bdn <- (binding << whitespaces << "->".! << whitespaces).?
      r <- bdn match {
        case Some(Right(b)) => for {
          t <- termImpl(using opt)(using ln union Set(b.name)) 
        } yield t.map(TFunction(b, _))
        case Some(Left(e)) => pure(Left(e))
        case None => app
      }
    } yield r
  }

  def term(using ns: Namespace) = P { termImpl(using ParsingOptions())(using Set())(using ns) }
}

private case class ParsingOptions(val appDelimiter: Parser[?] = space*)

private type LocalNames = Set[String]
