package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName

trait Namespace extends Iterable[(String, NamespaceElement)]{
  def get(name: String) : Option[NamespaceElement]
}

enum NamespaceElement {
  case Sub(ns: Namespace)
  case Leaf(qn: QualifiedName)
}

import NamespaceElement._

class InMemoryNamespace extends Namespace {
  import QualifiedName.{_, given _}
  import scala.language.implicitConversions
  import io.github.tgeng.stalker.core.tt._
  import scala.collection.mutable.Map
 
  private val content = Map[String, NamespaceElement]()

  override def get(name: String) = content.get(name)

  override def iterator: Iterator[(String, NamespaceElement)] = content.iterator

  def importDefinition(d: PreDefinition) = d.qn match {
    case _ / name => this(name) = d.qn
    case _ => ()
  }

  def update(name: String, qn: QualifiedName): Unit = update(name, Leaf(qn))
  def update(name: String, ns: Namespace): Unit = update(name, Sub(ns))
  def update(name: String, elem: NamespaceElement): Unit = content(name) = elem 

  def render(qn: QualifiedName): String = {
    ???
  }
}

object InMemoryNamespace {
  def create = {
    import io.github.tgeng.stalker.core.tt.builtins._
    val r = InMemoryNamespace()
    r.importDefinition(levelType)
    r.importDefinition(universeType)
    r.importDefinition(lsucFn)
    r.importDefinition(lmaxFn)
    r.importDefinition(idType)
    r
  }
}