package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.core.common.Namespace
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

  given FT[FTerm, Term] {
    def (f: FTerm) ttImpl (using ctx: LocalIndices)(using ns: Namespace) : Result[Term] = f match {
      case _ => ???
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