package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt._

trait FT[F, T] {
  def (f: F) tt (using ns: Namespace) : Result[T] = f.ttImpl(using LocalIndices())

  def (f: F) ttImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[T]
}

trait TF[T, F] {
  def (t: T) fe(using ns: Namespace) : F = t.feImpl(using LocalNames())

  def (t: T) feImpl(using localVars: LocalNames)(using ns: Namespace) : F
}

object conversion {
  import FTerm._
  import FElimination._
  import Term._
  import Whnf._
  import Elimination._

  given FT[FTerm, Term] {
    def (f: FTerm) ttImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Term] = f match {
      case FTFunction(arg, bodyTy) => for arg <- arg.ttImpl
                                          bodyTy <- ctx.withName(arg.name) { bodyTy.ttImpl } 
                                      yield TWhnf(WFunction(arg, bodyTy))
      case FTCon(name, args) => for args <- args.liftMap(_.ttImpl)
                                yield TWhnf(WCon(name, args))
      case FTLevel(level) => Right(TWhnf(WLevel(level, Set.empty)))
      case FTQRedux(qn, elims) => for elims <- elims.liftMap(_.ttImpl)
                                  yield TRedux(qn, elims)
      case FTRedux(head, names, elims) => ctx.get(head) match {
        case Right(idx) => for elims <- elims.liftMap(_.ttImpl)
                          yield TWhnf(WVar(idx, names.map(EProj(_)) ++ elims))
        case _ => ns.get(head) match {
          case Right(ns) => resolveInNamespace(ns, names) match {
            case (qn, names) => for elims <- elims.liftMap(_.ttImpl)
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
    def (f: FElimination) ttImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Elimination] = f match {
      case FETerm(t) => for t <- t.ttImpl
                        yield ETerm(t)
      case FEProj(p) => Right(EProj(p))
    }
  }

  given FT[FBinding, Binding[Term]] {
    def (b: FBinding) ttImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Binding[Term]] = b match {
      case FBinding(name, ty) => ty.ttImpl.map(Binding(_)(name))
    }
  }
}

private class LocalIndices {
  import scala.collection.mutable.Map
  import scala.collection.mutable.ArrayBuffer

  val indices = Map[String, ArrayBuffer[Int]]()
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

private class LocalNames {
  import scala.collection.mutable.ArrayBuffer

  val names = ArrayBuffer[String]()

  def get(idx: Int) : String = names(idx)
  def withName[T](name: String)(action: => T) : T = {
    names.prepend(name)
    val r = action
    names.dropInPlace(1)
    r
  }
}