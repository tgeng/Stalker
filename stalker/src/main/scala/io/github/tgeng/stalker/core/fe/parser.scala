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
  private val level = P { "[0-9]+".rp.map(s => FTLevel(Integer.parseInt(s))) << "lv" }

  private def name(using opt: ParsingOptions) = P { 
    {
      var p = s"$headPattern$bodyPattern*".rp
      if (opt.skipWhereAtLineEnd) {
        p = p & not("where" << spaces << newline)
      }
      p
    }.withFilter(!Set("->", ":", "=", "_").contains(_)) 
  }

  private def qn(using opt: ParsingOptions) = P { name sepBy1 '.' map (_.toList) }

  private def con(using opt: ParsingOptions)(using IndentRequirement) : Parser[FTerm] = P {
    for {
      n <- name
      args <- '{' >> whitespaces >> (atom sepBy whitespaces) << whitespaces << '}'
    } yield FTCon(n, args.toList)
  }

  private def ref(using opt: ParsingOptions)(using IndentRequirement) : Parser[FTerm] = P {
    for qn <- qn
    yield qn match {
      case head :: tail => FTRedux(head, tail, Nil)
      case _ => throw AssertionError()
    }
  }

  private def atom(using opt: ParsingOptions)(using IndentRequirement) : Parser[FTerm] = P {
    '(' >>! whitespaces >> termImpl(using opt.copy(appDelimiter = whitespaces)) << whitespaces << ')' | con | ref | level
  }

  private def proj(using opt: ParsingOptions) = '.' >>! name

  private def elim(using opt: ParsingOptions)(using IndentRequirement) : Parser[FElimination] = P {
    atom.map(FETerm(_)) | proj.map(p => FEProj(p))
  }

  private def app(using opt: ParsingOptions)(using IndentRequirement) : Parser[FTerm] = P {
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

  private def bindingImpl(using opt: ParsingOptions)(using IndentRequirement) : Parser[FBinding] = P {
    lift(name << whitespaces, ':' >>! whitespaces >> termImpl).map((x, ty) => FBinding(x, ty))
  }

  private def argTy(using opt: ParsingOptions)(using IndentRequirement) : Parser[FBinding] = P {
    '(' >> whitespaces >> bindingImpl << whitespaces << ')' | 
    app.map(FBinding("", _))
  }

  private def termImpl(using opt: ParsingOptions)(using IndentRequirement) : Parser[FTerm] = P {
    for {
      bdn <- (argTy << whitespaces << "->" <<! whitespaces).?
      r <- bdn match {
        case Some(b) => for t <- termImpl(using opt) yield FTFunction(b, t)
        case None => app
      }
    } yield r
  }

  def term = P { termImpl(using ParsingOptions())(using IndentRequirement(0)) }
  def binding = P { bindingImpl(using ParsingOptions())(using IndentRequirement(0)) }

  import FPattern._
  import FCoPattern._

  def pConApp(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    for forced <- "..".?
        qn <- qn << opt.appDelimiter
        args <- pAtom sepBy1 opt.appDelimiter
    yield FPCon(qn, args.toList, forced.isDefined)
  }

  def pConRaw(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    for forced <- "..".?
        con <- name
        args <- '{' >>! whitespaces >> (pAtom sepBy whitespaces) << whitespaces << '}'
    yield FPCon(con, args.toList, forced.isDefined)
  }

  def pattern(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    pConApp | pAtom
  }

  def pAtom(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    pConRaw |
    qn.map{ names =>
      if (names.size == 1) {
        FPVarCon(names(0))
      } else {
        FPCon(names, Nil, false)
      }
    } |
    "()".as(FPAbsurd) |
    '(' >>! whitespaces >> pattern(using opt.copy(appDelimiter = whitespaces)) << whitespaces << ')' |
    ".." >>! atom.map(FPForced(_))
  }

  def qProj(using opt: ParsingOptions) : Parser[FCoPattern] = P {
    proj.map(FQProj(_))
  }

  def qAtom(using opt: ParsingOptions)(using IndentRequirement) : Parser[FCoPattern] = P {
    pAtom.map(FQPattern(_)) | qProj
  }

  def coPatterns : Parser[List[FCoPattern]] = P {
    given ParsingOptions = ParsingOptions()
    given IndentRequirement = IndentRequirement(0)
    qAtom sepBy spaces map (_.toList)
  }

  def constructor(using opt: ParsingOptions)(using IndentRequirement) : Parser[FConstructor] = P {
    for n <- name
        _ <- spaces >> ':' <<! spaces
        argTys <- aligned {
          (argTy << whitespaces << "->" << whitespaces)
        }.*
        _ <- termImpl // ignored for now since indexed family is simulated with id type
    yield FConstructor(n, argTys.toList)
  }

  def constructors(using opt: ParsingOptions)(using IndentRequirement) : Parser[Seq[FConstructor]] = P {
    for _ <- "where" << someLines << spaces
        cons <- constructor sepBy (someLines << spaces)
    yield cons
  }

  import FDeclaration._
  def data : Parser[FData] = P { 
    given ParsingOptions = ParsingOptions()
    alignedWithIndent(1) {
      for n <- "data" >> spaces >> name
          _ <- spaces >> ':' <<! spaces
          argTys <- aligned {
            (argTy << whitespaces << "->" << whitespaces).*
          }
          ty <- termImpl(using ParsingOptions(skipWhereAtLineEnd = true))
          cons <- (spaces >> constructors).?
      yield new FData(n, argTys.toList, ty, cons.orNull)
    }
  }

  def declaration : Parser[FDeclaration] = P { data }

}

private case class ParsingOptions(val appDelimiter: Parser[?] = spaces, val skipWhereAtLineEnd: Boolean = false)
