package io.github.tgeng.stalker.common

import scala.language.implicitConversions

enum QualifiedName {
  case Root
  case Sub(val parent: QualifiedName, val name: String)

  override def toString: String = this match {
    case Root => throw UnsupportedOperationException("toString method cannot be overwritten for the singleton Root")
    case Sub(Root, name) => "." + name
    case Sub(parent, name) => parent.toString + "." + name
  }

  def / (subName: String) : QualifiedName = QualifiedName.Sub(this, subName)
}

object QualifiedName {
  given Conversion[String, QualifiedName] = s => s.split('.').foldLeft(Root)(_/_)
}
