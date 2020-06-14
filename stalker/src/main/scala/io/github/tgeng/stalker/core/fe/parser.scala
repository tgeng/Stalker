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
  private val num : Parser[FTerm] = P { 
    for i <- "[0-9]+".rp.map(s => Integer.parseInt(s))
        levelSuffix <- "lv".?
    yield levelSuffix match {
      case Some(_) => FTLevel(i)
      case None => FTNat(i)
    }
  }

  private def name(using opt: ParsingOptions) = P { 
    {
      var p = s"$headPattern$bodyPattern*".rp
      if (opt.skipWhereAtLineEnd) {
        p = p & not("where" << spaces << (newline | eof))
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
    '(' >>! whitespaces >> termImpl(using opt.copy(appDelimiter = whitespaces)) << whitespaces << ')' | con | ref | num
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
          case (FTNat(_), _) => fail("Cannot apply to a Nat.")
        }
      }
    }
  }

  private def bindingImpl(using opt: ParsingOptions)(using IndentRequirement) : Parser[FBinding] = P {
    lift(name << whitespaces, ':' >>! whitespaces >> termImpl).map((x, ty) => FBinding(x, ty))
  }

  private def namedArgTy(using opt: ParsingOptions)(using IndentRequirement) : Parser[FBinding] = P {
    '(' >> whitespaces >> bindingImpl << whitespaces << ')'
  }

  private def argTy(using opt: ParsingOptions)(using IndentRequirement) : Parser[FBinding] = P {
    namedArgTy | app.map(FBinding("", _))
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

  private def pConApp(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    for forced <- "..".?
        qn <- qn << opt.appDelimiter
        args <- pAtom sepBy1 opt.appDelimiter
    yield FPCon(qn, args.toList, forced.isDefined)
  }

  private def pConRaw(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    for forced <- "..".?
        con <- name
        args <- '{' >>! whitespaces >> (pAtom sepBy whitespaces) << whitespaces << '}'
    yield FPCon(con, args.toList, forced.isDefined)
  }

  private def pattern(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
    pConApp | pAtom
  }

  private def pAtom(using opt: ParsingOptions)(using IndentRequirement) : Parser[FPattern] = P {
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

  private def qProj(using opt: ParsingOptions) : Parser[FCoPattern] = P {
    proj.map(FQProj(_))
  }

  private def qAtom(using opt: ParsingOptions)(using IndentRequirement) : Parser[FCoPattern] = P {
    pAtom.map(FQPattern(_)) | qProj
  }

  private def coPatternsImpl(using opt: ParsingOptions)(using IndentRequirement) : Parser[List[FCoPattern]] = P {
    qAtom sepBy spaces map (_.toList)
  }

  def coPatterns : Parser[List[FCoPattern]] = P {
    given ParsingOptions = ParsingOptions()
    given IndentRequirement = IndentRequirement(0)
    coPatternsImpl
  }

  import FDeclaration._

  private def constructor(using opt: ParsingOptions)(using IndentRequirement) : Parser[FConstructor] = P {
    for n <- name
        _ <- spaces >> ':' <<! spaces
        argTys <- aligned {
          (argTy << whitespaces << "->" << whitespaces)
        }.*
        _ <- termImpl // ignored for now since indexed family is simulated with id type
    yield FConstructor(n, argTys.toList)
  }

  private def schemaType(using opt: ParsingOptions)(using IndentRequirement) : Parser[(Seq[FBinding], FTerm)] = P {
    for argTys <- namedArgTy sepBy whitespaces
        _ <- spaces >> ':' <<! spaces
        ty <- termImpl(using ParsingOptions(skipWhereAtLineEnd = true))
    yield (argTys, ty)
  }

  private def data(using opt: ParsingOptions)(using IndentRequirement) : Parser[FDeclaration] = P { 
    for n <- "data " >>! spaces >> name << spaces
        st <- schemaType.?
        cons <- (spaces >> whereSomething(constructor)).?
        r <- (st, cons) match {
          case (Some(argTys, ty), cons) => pure(FData(n, argTys.toList, ty, cons.orNull))
          case (None, Some(cons)) => pure(FDataDef(n, cons))
          case (None, None) => fail("A data declaration must have at least a type declaration or constructor declarations.")
        }
    yield r
  }

  private def field(using opt: ParsingOptions)(using IndentRequirement) : Parser[FField] = P {
    for n <- name
        _ <- spaces >> ':' <<! spaces
        ty <- termImpl 
    yield FField(n, ty)
  }

  private def record(using opt: ParsingOptions)(using IndentRequirement) : Parser[FDeclaration] = P { 
    for n <- "record " >>! spaces >> name << spaces
        st <- schemaType.?
        fields <- (spaces >> whereSomething(field)).?
        r <- (st, fields) match {
          case (Some(argTys, ty), fields) => pure(FRecord(n, argTys.toList, ty, fields.orNull))
          case (None, Some(fields)) => pure(FRecordDef(n, fields))
          case (None, None) => fail("A record declaration must have at least a type declaration or field declarations.")
        }
    yield r
  }

  private def whereSomething[T](something: Parser[T]) : Parser[Seq[T]] = {
    for _ <- commitAfter("where")
        s <- (spaces >> someLines >> spaces >> something).*
    yield s
  }

  import FUncheckedRhs._

  private def clause(using opt: ParsingOptions)(using IndentRequirement) : Parser[FUncheckedClause] = P {
    for lhs <- coPatternsImpl
        rhs <- (spaces >> "=" >>! spaces >> termImpl).?
    yield rhs match {
      case Some(rhs) => FUncheckedClause(lhs, FUTerm(rhs))
      case None => FUncheckedClause(lhs, FUImpossible)
    }
  }

  private def definition(using opt: ParsingOptions)(using IndentRequirement) : Parser[FDeclaration] = P {
    for n <- "def " >>! spaces >> name << spaces << ":" <<! spaces
        ty <- termImpl
        clauses <- (spaces >> someLines >> spaces >> clause).*
    yield FDefinition(n, ty, clauses)
  }

  def declaration : Parser[FDeclaration] = P { 
    given ParsingOptions = ParsingOptions()
    alignedWithIndent(1) {
      data | record | definition
    }
  }
}

private case class ParsingOptions(val appDelimiter: Parser[?] = spaces, val skipWhereAtLineEnd: Boolean = false)
