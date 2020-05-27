package io.github.tgeng.stalker.common

import scala.language.implicitConversions

enum QualifiedName {
  case Root
  case /(val parent: QualifiedName, val name: String)

  override def toString: String = this match {
    case Root => throw AssertionError("toString method cannot be overwritten for the singleton Root so this case should never be invoked")
    case Root / name => name
    case parent / name => parent.toString + "." + name
  }
}

import QualifiedName._

object QualifiedName {
  def (qn: QualifiedName) / (name: String) : QualifiedName = /(qn, name)
  given qn as Conversion[String, QualifiedName] = s => s.split('.').foldLeft(Root)(_ / _)
}
