package io.github.tgeng.stalker.core.fe

import scala.language.postfixOps
import scala.language.implicitConversions
import scala.collection.Map
import io.github.tgeng.common.extraSeqOps._
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

object parser {
  import FTerm._
  import FElimination._

  private val bodyInvalidChars = " \\r\\n\\t()\\[\\]{}."
  private val bodyPattern = s"[^${bodyInvalidChars}]"
  private val headPattern = s"""[^`'"0-9${bodyInvalidChars}]"""
  private val name = P { s"$headPattern$bodyPattern*".rp.withFilter(!Set("->", ":", "=", "_").contains(_)) }
  private val level = P { "[0-9]+".rp.map(s => FTLevel(Integer.parseInt(s))) << "lv" }
  private val qn = P { name sepBy1 '.' map (_.toList) }

  private def con(using opt: ParsingOptions) : Parser[FTerm] = P {
    for {
      n <- name
      args <- '{' >> whitespaces >> (atom sepBy whitespaces) << whitespaces << '}'
    } yield FTCon(n, args.toList)
  }

  private def ref(using opt: ParsingOptions) : Parser[FTerm] = P {
    for qn <- qn
    yield qn match {
      case head :: tail => FTRedux(head, tail, Nil)
      case _ => throw AssertionError()
    }
  }

  private def atom(using opt: ParsingOptions) : Parser[FTerm] = P {
    '(' >>! whitespaces >> termImpl(using opt.copy(appDelimiter = whitespaces)) << whitespaces << ')' | con | ref | level
  }

  private def proj = '.' >>! name

  private def elim(using opt: ParsingOptions) : Parser[FElimination] = P {
    atom.map(FETerm(_)) | proj.map(p => FEProj(p))
  }

  private def app(using opt: ParsingOptions) : Parser[FTerm] = P {
    lift(atom, (opt.appDelimiter >> elim).*).flatMap {
      case (t, elims) => if (elims.isEmpty) {
        pure(t)
      } else {
        (t, elims) match {
          case (FTRedux(head, name, es1), es2) => pure(FTRedux(head, name, es1 ++ es2))
          case (FTFunction(_, _), _) => fail("Cannot apply to function type.")
          case (FTLevel(_), _) => fail("Cannot apply to a level.")
          case (FTCon(_, _), _) => fail("Cannot apply to a constructed value.")
        }
      }
    }
  }

  private def bindingImpl(using opt: ParsingOptions) : Parser[FBinding] = P {
    lift(name << whitespaces, ':' >>! whitespaces >> termImpl).map((x, ty) => FBinding(x, ty))
  }

  private def arg(using opt: ParsingOptions) : Parser[FBinding] = P {
    '(' >> whitespaces >> bindingImpl << whitespaces << ')' | 
    app.map(FBinding("", _))
  }

  private def termImpl(using opt: ParsingOptions) : Parser[FTerm] = P {
    for {
      bdn <- (arg << whitespaces << "->" <<! whitespaces).?
      r <- bdn match {
        case Some(b) => for t <- termImpl(using opt) yield FTFunction(b, t)
        case None => app
      }
    } yield r
  }

  def term = P { termImpl(using ParsingOptions()) }
  def binding = P { bindingImpl(using ParsingOptions()) }

  import FPattern._
  import FCoPattern._

  def pConWithArgs(using opt: ParsingOptions) : Parser[FPattern] = P {
    for forced <- "..".?
        qn <- qn << opt.appDelimiter
        args <- patternImpl sepBy1 opt.appDelimiter
    yield forced match {
      case Some(_) => FPForcedCon(qn, args.toList)
      case None => FPCon(qn, args.toList)
    }
  }

  def patterns(using opt: ParsingOptions) : Parser[FPattern] = P {
    pConWithArgs | patternImpl
  }

  def patternImpl(using opt: ParsingOptions) : Parser[FPattern] = P {
    qn.map{ names =>
      if (names.size == 1) {
        FPVarCon(names(0))
      } else {
        FPCon(names, Nil)
      }
    } |
    "()".as(FPAbsurd) |
    '(' >>! whitespaces >> patterns(using opt.copy(appDelimiter = whitespaces)) << whitespaces << ')' |
    ".." >>! atom.map(FPForced(_))
  }

  def qProj : Parser[FCoPattern] = P {
    proj.map(FQProj(_))
  }

  def coPatternImpl(using opt: ParsingOptions) : Parser[FCoPattern] = P {
    patternImpl.map(FQPattern(_)) | qProj
  }

  def coPatterns : Parser[List[FCoPattern]] = P {
    given ParsingOptions = ParsingOptions()
    coPatternImpl sepBy spaces map (_.toList)
  }
}

private case class ParsingOptions(val appDelimiter: Parser[?] = spaces)
