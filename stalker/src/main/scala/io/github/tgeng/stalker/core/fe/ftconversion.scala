package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import io.github.tgeng.common.eitherOps
import io.github.tgeng.stalker.common.nsElemSetOps
import io.github.tgeng.stalker.common._
import io.github.tgeng.stalker.common.Error._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.tt._

import QualifiedName._

trait FT[F, T] {
  def (f: F) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[T]
}

trait FTWithQualifiedName[F, T] {
  def (f: F) toTt(qn: QualifiedName)(using ns: Namespace) : Result[T]
}

object ftConversion {
  import FTerm._
  import FElimination._
  import Term._
  import Whnf._
  import Elimination._
  import FPattern._
  import Pattern._
  import FCoPattern._
  import CoPattern._

  given FT[FTerm, Term] {
    def (f: FTerm) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[Term] = f match {
      case FTFunction(arg, bodyTy) => for arg <- arg.toTt
                                          bodyTy <- ctx.withName(arg.name) { bodyTy.toTt } 
                                      yield TWhnf(WFunction(arg, bodyTy))
      case FTCon(name, args) => for args <- args.liftMap(_.toTt)
                                yield TWhnf(WCon(name, args))
      case FTLevel(level) => Right(TWhnf(WLConst(level)))
      case FTNat(n) => Right((0 until n).foldLeft(TRedux("stalker.data.Nat.Zero", Nil))((acc, _) => TRedux("stalker.data.Nat.Suc", List(ETerm(acc)))))
      case FTRedux(names, elims) => names match {
        case name :: Nil if ctx.get(name).isRight => 
          for elims <- elims.liftMap(_.toTt)
          yield TWhnf(WVar(ctx.get(name).!!!, elims))
        case _ => for qns <- ns.resolve(names)
                      qn <- qns.uniqueQualifiedName(names)
                      elims <- elims.liftMap(_.toTt)
                  yield TRedux(qn, elims)
      }
    }
  }

  given FT[FElimination, Elimination] {
    def (f: FElimination) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[Elimination] = f match {
      case FETerm(t) => for t <- t.toTt yield ETerm(t)
      case FEProj(p) => Right(EProj(p))
    }
  }

  given FT[FBinding, Binding[Term]] {
    def (b: FBinding) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[Binding[Term]] = b match {
      case FBinding(name, ty) => ty.toTt.map(Binding(_)(name))
    }
  }

  given FT[FTelescope, List[Binding[Term]]] {
    def (ts: FTelescope) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[List[Binding[Term]]] = ts match {
      case Nil => Right(Nil)
      case b :: rest => 
        for b <- b.toTt
          rest <- ctx.withName(b.name) { rest.toTt }
        yield b :: rest
    }
  }

  given FT[FPattern, Pattern] {
    def (p: FPattern) toTt (using ctx:LocalFtCtx)(using ns: Namespace) : Result[Pattern] = p match {
      case FPVar(name) => for idx <- ctx.get(name)
                          yield PVar(idx)(name)
      case FPCon(con: String, args, forced) =>
        for args <- args.liftMap(_.toTt) 
        yield forced match {
          case true => PCon(con, args)
          case false => PForcedCon(con, args)
        }
      case FPForced(t) => for t <- t.toTt yield PForced(t)
      case FPAbsurd => Right(PAbsurd)
    }
  }

  given FT[FCoPattern, CoPattern] {
    def (q: FCoPattern) toTt (using ctx:LocalFtCtx)(using ns: Namespace) : Result[CoPattern] = q match {
      case FQPattern(p) => for p <- p.toTt yield QPattern(p)
      case FQProj(p) => Right(QProj(p))
    }
  }

  import PreDeclaration._
  import FDeclaration._
  import FUncheckedRhs._
  import UncheckedRhs._

  given FTWithQualifiedName[FDeclaration, PreDeclaration] {
    def (d: FDeclaration) toTt(qn: QualifiedName)(using ns: Namespace) : Result[PreDeclaration] = d match {
      case d: FData => d.toTt(qn)
      case r: FRecord => r.toTt(qn)
      case d: FDefinition => d.toTt(qn)
    }
  }

  given FTWithQualifiedName[FData, PreData] {
    def (d: FData) toTt(qn: QualifiedName)(using ns: Namespace) : Result[PreData] = {
      given LocalFtCtx = LocalFtCtx()
      d match {
        case FData(name, paramTys, ty, cons) => for {
          paramTys <- paramTys.toTt
          r <- summon[LocalFtCtx].withNames(paramTys.map(_.name)) {
            for ty <- ty.toTt
                cons <- cons match {
                  case cons : Seq[FConstructor] => {
                    cons.liftMap(_.toTt)
                  }
                }
            yield new PreData(qn / name)(paramTys, ty, cons)
          }
        } yield r
      }
    }
  }

  given FT[FConstructor, PreConstructor] {
    def (c: FConstructor) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[PreConstructor] = c match {
      case FConstructor(name, argTys) =>
        for argTys <- argTys.toTt
        yield PreConstructor(name, argTys)
    }
  }

  given FTWithQualifiedName[FRecord, PreRecord] {
    def (r: FRecord) toTt(qn: QualifiedName)(using ns: Namespace) : Result[PreRecord] = {
      given LocalFtCtx = LocalFtCtx()
      r match {
        case FRecord(name, paramTys, ty, fields) => for {
          paramTys <- paramTys.toTt
          r <- summon[LocalFtCtx].withNames(paramTys.map(_.name) :+ "self") {
            for ty <- ty.toTt
                fields <- fields match {
                  case fields : Seq[FField] => fields.liftMap(_.toTt)
                }
            yield new PreRecord(qn / name)(paramTys, ty, fields)
          }
        } yield r
      }
    }
  }

  given FTWithQualifiedName[FDefinition, PreDefinition] {
    def (d: FDefinition) toTt(qn: QualifiedName)(using ns: Namespace) : Result[PreDefinition] = {
      given LocalFtCtx = LocalFtCtx()
      d match {
        case FDefinition(name, ty, clauses) => for {
          ty <- ty.toTt
          clauses <- clauses.liftMap(_.toTt)
        } yield new PreDefinition(qn / name)(ty, clauses)
      }
    }
  }

  given FT[FField, PreField] {
    def (c: FField) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[PreField] = c match {
      case FField(name, ty) =>
        for ty <- ty.toTt
        yield PreField(name, ty)
    }
  }

  given FT[FUncheckedRhs, UncheckedRhs] {
    def (c: FUncheckedRhs) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[UncheckedRhs] = c match {
      case FUTerm(t) => for t <- t.toTt yield UTerm(t)
      case FUImpossible => Right(UImpossible)
    }
  }

  given FT[FUncheckedClause, UncheckedClause] {
    def (c: FUncheckedClause) toTt (using ctx: LocalFtCtx)(using ns: Namespace) : Result[UncheckedClause] = {
      assert(ctx.size == 0)
      c match {
        case FUncheckedClause(lhs, rhs) => {
          val ctx = LocalFtCtx()
          ctx.addAllFromCoPatterns(lhs)
          given LocalFtCtx = ctx
          for lhs <- lhs.liftMap(_.toTt)
              rhs <- rhs.toTt
          yield UncheckedClause(lhs, rhs)
        }
      }
    }
  }
}

class LocalFtCtx(content: Map[String, Int] = Map.empty) {
  import scala.collection.mutable.Map
  import scala.collection.mutable.ArrayBuffer

  val indices : Map[String, ArrayBuffer[Int]] = Map.from(content.view.mapValues(ArrayBuffer(_)))
  var size : Int = 0

  def get(name: String) : Result[Int] = indices.get(name).flatMap(_.lastOption) match {
    case Some(i) => Right(size - i)
    case None => noNameError(e"Cannot find local variable $name.")
  }

  def add(name: String) = {
    size += 1
    val buffer = indices.getOrElseUpdate(name, ArrayBuffer())
    buffer += size
  }

  def withName[T](name: String)(action: => T) : T = {
    size += 1
    val buffer = indices.getOrElseUpdate(name, ArrayBuffer())
    buffer += size
    val t = action
    buffer.dropRightInPlace(1)
    if (buffer.isEmpty) {
      indices.remove(name)
    }
    size -= 1
    t
  }

  def withNames[T](names: List[String])(action: => T) : T = names match {
    case Nil => action
    case name :: rest => withName(name) {
      withNames(rest) {
        action
      }
    }
  }

  def addAllFromCoPatterns(coPatterns: Seq[FCoPattern])(using ns: Namespace) : Unit = {
    import FCoPattern._
    addAllFromPatterns(for case FQPattern(p) <- coPatterns yield p)
  }

  def addAllFromPatterns(patterns: Seq[FPattern])(using ns: Namespace) : Unit = {
    import FPattern._
    patterns.foreach {
      case FPVar(name) => {
        get(name) match {
          case Right(_) => ()
          case _ => add(name)
        }
      }
      case FPCon(_, args, _) => addAllFromPatterns(args)
      case FPForced(t: FTerm) => ()
      case FPAbsurd => ()
    }
  }

  override def toString = indices.view.mapValues(_.last).toMap.toString
}

import scala.collection.Set

private def (nsElems: Set[NsElem]) uniqueQualifiedName(names: Seq[String]): Result[QualifiedName] = {
  val qns = nsElems.qualifiedNames
  if (qns.isEmpty) {
    noNameError(e"$names does not reference a valid definition.")
  } else if (qns.size == 1) {
    Right(qns.head)
  } else {
    ambiguousNameError(e"$names references multiple different definitions $qns.")
  }
}