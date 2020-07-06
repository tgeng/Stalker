package io.github.tgeng.stalker.common

import scala.language.implicitConversions

enum QualifiedName {
  case Root
  case /(override val parent: QualifiedName, val name: String)

  def parent : QualifiedName = this match {
    case Root => Root
    case parent / _ => parent
  }

  override def toString: String = this match {
    case Root => throw AssertionError("toString method cannot be overwritten for the singleton Root so this case should never be invoked")
    case Root / name => name
    case parent / name => parent.toString + "." + name
  }

  /** 
   * Gets the parts in this qualified name. Note the first part in the returned
   * list is the lowest (rightmost) part in the qualified name.
   */
  def parts : List[String] = this match {
    case Root => Nil
    case parent / name => name :: parent.parts
  }

  def depth : Int = this match {
    case Root => 0
    case parent / _ => parent.depth + 1
  }

  /** Gets the relative name reference from that to this. Note the first part in
    * the returned list is the lowest (rightmost) part in the qualified name.
    */
  def - (that: QualifiedName) : Option[List[String]] = {
    val thisDepth = this.depth
    val thatDepth = that.depth
    val diff = thisDepth - thatDepth
    if (diff < 0) return None
    val thisPrefix = this.drop(diff)
    if (thisPrefix == that) {
      Some(parts.take(diff))
    } else {
      None
    }
  }

  def hasPrefix(that: QualifiedName) = (this - that).isDefined

  def drop(i: Int) : QualifiedName = (i, this) match {
    case (i, _) if (i <= 0) => this
    case (_, Root) => Root
    case (i, parent / _) => parent.drop(i)
  }
}

import QualifiedName._

object QualifiedName {
  def (qn: QualifiedName) / (name: String) : QualifiedName = /(qn, name)
  given qn as Conversion[String, QualifiedName] = s => s.split('.').foldLeft(Root)(_ / _)
  def fromNames(names: Iterable[String]) = names.foldLeft(Root)((parent, name) => parent / name)
}
