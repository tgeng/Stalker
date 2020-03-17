package io.github.tgeng.stalker.core

enum QualifiedName {
  case Root()
  case Sub(val parent: QualifiedName, val name: String)

  override def toString: String = this match {
    case Root() => ""
    case Sub(parent, name) => parent.toString + "." + name
  }

  def / (subName: String) : QualifiedName = QualifiedName.Sub(this, subName)
}

val root = QualifiedName.Root()
