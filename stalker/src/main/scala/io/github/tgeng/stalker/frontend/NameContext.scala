package io.github.tgeng.stalker.frontend

import scala.collection._

class NameContext {
  val indices = mutable.Map[String, mutable.ArrayBuffer[Int]]()
  var size : Int = 0

  def get(name: String) : Result[Int] = 
    indices.get(name).flatMap(_.lastOption).map(size - _) match {
      case Some(i) => Right(i)
      case _ => Left(NoNameError(name, this))
    }

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

  def withNames[T](names: List[String])(action: => T) : T = names match {
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

class NoNameError(name: String, ctx: NameContext)
type Result = Either[NoNameError, *]