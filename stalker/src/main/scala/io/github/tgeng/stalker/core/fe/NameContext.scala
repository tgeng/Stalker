package io.github.tgeng.stalker.core.fe

import scala.collection.mutable
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.common.QualifiedName

class NameContext {
  val indices = mutable.Map[String, mutable.ArrayBuffer[Int]]()
  var size : Int = 0

  def apply(name: String) = indices(name).last

  def withName[T](name: String)(action: => T) : T = {
    size += 1
    val buffer = indices.getOrElseUpdate(name, mutable.ArrayBuffer())
    buffer += size
    val t = action
    buffer.dropRightInPlace(1)
    size -= 1
    t
  }

  def withTelescope[T](telescope: Telescope)(action: => T) : T = withNames(telescope.map(_.name))(action)

  def withNames[T](names: Seq[String])(action: => T) : T = names.toList match {
    case Nil => action
    case name :: rest => withName(name) {
      withNames(rest)(action)
    }
  }

  override def toString() =
    if(indices.isEmpty) "<empty context>"
    else indices.map{(name, indices) =>
      s"$name: ${indices.map(size - _).mkString(" ")}"
    }.mkString("\n")
}

object NameContext {
  def empty = NameContext()
}