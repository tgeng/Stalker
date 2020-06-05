package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt._

trait FT[F, T] {
  def (f: F) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[T]
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
    def (f: FTerm) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[Term] = f match {
      case FTFunction(arg, bodyTy) => for arg <- arg.toTt
                                          bodyTy <- ctx.withName(arg.name) { bodyTy.toTt } 
                                      yield TWhnf(WFunction(arg, bodyTy))
      case FTCon(name, args) => for args <- args.liftMap(_.toTt)
                                yield TWhnf(WCon(name, args))
      case FTLevel(level) => Right(TWhnf(WLConst(level)))
      case FTRedux(head, names, elims) => ctx.get(head) match {
        case Right(idx) => for elims <- elims.liftMap(_.toTt)
                           yield TWhnf(WVar(idx, names.map(EProj(_)) ++ elims))
        case _ => ns.get(head) match {
          case Right(ns) => resolveInNamespace(ns, names) match {
            case (ns, names) => (ns, ns.getConstructorName, names) match {
              // TODO(tgeng): remove this special handling after implicit parameter
              // is supported so that constructor can be normal functions.
              case (ns, Right(con), names) => {
                names match {
                  case Nil =>
                    for args <- elims.liftMap {
                          case p : FEProj => typingError(e"Cannot apply projection $p to constructor ${ns.qn}.")
                          case FETerm(t) => Right(t)
                        }
                        args <- args.liftMap(_.toTt)
                    yield TWhnf(WCon(con, args))
                  case name :: _ => typingError(e"Cannot apply projection ${FEProj(name)} to constructor ${ns.qn}.")
                }
              }
              case (ns, _, names) =>
                for elims <- elims.liftMap(_.toTt)
                yield TRedux(ns.qn, names.map(EProj(_)) ++ elims)
            }

          }
          case _ => noNameError(e"$head is not a local variable nor a name in the current scope.")
        }
      }
    }
  }

  private def resolveInNamespace(ns: Namespace, names: List[String]): (Namespace, List[String]) = names match {
    case Nil => (ns, Nil)
    case name :: rest => ns.get(name) match {
      case Right(ns) => resolveInNamespace(ns, rest)
      case _ => (ns, names)
    }
  }

  given FT[FElimination, Elimination] {
    def (f: FElimination) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[Elimination] = f match {
      case FETerm(t) => for t <- t.toTt yield ETerm(t)
      case FEProj(p) => Right(EProj(p))
    }
  }

  given FT[FBinding, Binding[Term]] {
    def (b: FBinding) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[Binding[Term]] = b match {
      case FBinding(name, ty) => ty.toTt.map(Binding(_)(name))
    }
  }

  given FT[FTelescope, List[Binding[Term]]] {
    def (ts: FTelescope) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[List[Binding[Term]]] = ts.liftMap(_.toTt)
  }

  given FT[FPattern, Pattern] {
    def (p: FPattern) toTt (using ctx:LocalIndices)(using ns: Namespace) : Result[Pattern] = p match {
      case FPVarCon(name) => 
        (for conNs <- ns.get(name)
             con <- conNs.getConstructorName
         yield PCon(con, Nil)) match {
          case Left(_) => for idx <- ctx.get(name)
                          yield PVar(idx)(name)
          case r => r
        }

      case FPCon(con, args) => for args <- args.liftMap(_.toTt) 
                                   conNs <- ns.get(con)
                                   con <- conNs.getConstructorName
                               yield PCon(con, args)
      case FPForcedCon(con, args) => for args <- args.liftMap(_.toTt) 
                                   conNs <- ns.get(con)
                                   con <- conNs.getConstructorName
                               yield PForcedCon(con, args)
      case FPForced(t) => for t <- t.toTt yield PForced(t)
      case FPAbsurd => Right(PAbsurd)
    }
  }

  given FT[FCoPattern, CoPattern] {
    def (q: FCoPattern) toTt (using ctx:LocalIndices)(using ns: Namespace) : Result[CoPattern] = q match {
      case FQPattern(p) => for p <- p.toTt yield QPattern(p)
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

  def addAllFromCoPatterns(coPatterns: Seq[FCoPattern])(using ns: Namespace) : Unit = {
    import FCoPattern._
    addAllFromPatterns(for case FQPattern(p) <- coPatterns yield p)
  }

  def addAllFromPatterns(patterns: Seq[FPattern])(using ns: Namespace) : Unit = {
    import FPattern._
    patterns.foreach {
      case FPVarCon(name) => {
        get(name) match {
          case Right(_) => ()
          case _ => (for conNs <- ns.get(name)
                         con <- conNs.getConstructorName
                    yield ()) match {
                      case Left(_) => add(name)
                      case _ => ()
                    }
        }
      }
      case FPCon(_, args) => addAllFromPatterns(args)
      case FPForcedCon(_, args) => addAllFromPatterns(args)
      case FPForced(t: FTerm) => ()
      case FPAbsurd => ()
    }
  }

  override def toString = indices.view.mapValues(_.last).toMap.toString
}
