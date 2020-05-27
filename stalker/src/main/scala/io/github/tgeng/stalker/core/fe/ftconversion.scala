package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt._

trait FT[F, T] {
  def (f: F) toTt (using ns: Namespace) : Result[T] = f.toTtImpl(using LocalIndices())

  def (f: F) toTtImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[T]
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
    def (f: FTerm) toTtImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Term] = f match {
      case FTFunction(arg, bodyTy) => for arg <- arg.toTtImpl
                                          bodyTy <- ctx.withName(arg.name) { bodyTy.toTtImpl } 
                                      yield TWhnf(WFunction(arg, bodyTy))
      case FTCon(name, args) => for args <- args.liftMap(_.toTtImpl)
                                yield TWhnf(WCon(name, args))
      case FTLevel(level) => Right(TWhnf(WLevel(level, Set.empty)))
      case FTRedux(head, names, elims) => ctx.get(head) match {
        case Right(idx) => for elims <- elims.liftMap(_.toTtImpl)
                          yield TWhnf(WVar(idx, names.map(EProj(_)) ++ elims))
        case _ => ns.get(head) match {
          case Right(ns) => resolveInNamespace(ns, names) match {
            case (qn, names) => for elims <- elims.liftMap(_.toTtImpl)
                                yield TRedux(qn, names.map(EProj(_)) ++ elims)
          }
          case _ => noNameError(s"$head is not a local variable nor a name in the current scope.")
        }
      }
    }
  }

  private def resolveInNamespace(ns: Namespace, names: List[String]): (QualifiedName, List[String]) = names match {
    case Nil => (ns.qn, Nil)
    case name :: rest => ns.get(name) match {
      case Right(ns) => resolveInNamespace(ns, rest)
      case _ => (ns.qn, names)
    }
  }

  given FT[FElimination, Elimination] {
    def (f: FElimination) toTtImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Elimination] = f match {
      case FETerm(t) => for t <- t.toTtImpl yield ETerm(t)
      case FEProj(p) => Right(EProj(p))
    }
  }

  given FT[FBinding, Binding[Term]] {
    def (b: FBinding) toTtImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Binding[Term]] = b match {
      case FBinding(name, ty) => ty.toTtImpl.map(Binding(_)(name))
    }
  }

  given FT[FTelescope, List[Binding[Term]]] {
    def (ts: FTelescope) toTtImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[List[Binding[Term]]] = ts.liftMap(_.toTtImpl)
  }

  given FT[FPattern, Pattern] {
    def (p: FPattern) toTtImpl (using ctx:LocalIndices)(using ns: Namespace) : Result[Pattern] = p match {
      case FPVar(name) => for idx <- ctx.get(name) yield PVar(idx)(name)
      case FPCon(con, args) => for args <- args.liftMap(_.toTtImpl) yield PCon(con, args)
      case FPForcedCon(con, args) => for args <- args.liftMap(_.toTtImpl) yield PForcedCon(con, args)
      case FPForced(t) => for t <- t.toTtImpl yield PForced(t)
      case FPAbsurd => Right(PAbsurd)
    }
  }

  given FT[FCoPattern, CoPattern] {
    def (q: FCoPattern) toTtImpl (using ctx:LocalIndices)(using ns: Namespace) : Result[CoPattern] = q match {
      case FQPattern(p) => for p <- p.toTtImpl yield QPattern(p)
      case FQProj(p) => Right(QProj(p))
    }
  }
}

class LocalIndices(content: Map[String, Int] = Map.empty) {
  import scala.collection.mutable.Map
  import scala.collection.mutable.ArrayBuffer

  val indices : Map[String, ArrayBuffer[Int]] = Map.from(content.view.mapValues(ArrayBuffer(_)))
  var size : Int = 0

  def get(name: String) : Result[Int] = indices.get(name).flatMap(_.lastOption) match {
    case Some(i) => Right(i)
    case None => noNameError(s"Cannot find local variable $name.")
  }

  def withName[T](name: String)(action: => T) : T = {
    size += 1
    val buffer = indices.getOrElseUpdate(name, ArrayBuffer())
    buffer += size
    val t = action
    buffer.dropRightInPlace(1)
    size -= 1
    t
  }
}
