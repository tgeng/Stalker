package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName

trait Namespace extends Iterable[(String, NamespaceElement[Namespace])]{
  def get(name: String) : Option[NamespaceElement[Namespace]]
}

enum NamespaceElement[+T] {
  case Sub(namespace: T)
  case Leaf(qn: QualifiedName)
}

import NamespaceElement._

class MutableNamespace extends Namespace {
  import QualifiedName.{_, given _}
  import scala.language.implicitConversions
  import io.github.tgeng.stalker.core.tt._
 
  private val content = scala.collection.mutable.Map[String, NamespaceElement[MutableNamespace]]()

  override def get(name: String) = content.get(name)

  override def iterator: Iterator[(String, NamespaceElement[Namespace])] = content.iterator

  def importDefinition(d: PreDefinition) = d.qn match {
    case _ / name => this(name) = d.qn
    case _ => ()
  }

  def update(name: String, qn: QualifiedName) = content(name) = Leaf(qn)
  
  def incorporate(namespace: Namespace) : MutableNamespace = {
    namespace.foreach{
      case (k, v) => content(k) = (content.get(k), v) match {
        case (Some(Sub(ns1)), Sub(ns2)) => Sub(ns1.incorporate(ns2))
        case (_, Sub(ns)) => Sub(MutableNamespace().incorporate(ns))
        case (_, Leaf(qn)) => Leaf(qn)
      }
    }
    this
  }
}

object MutableNamespace {
  def create = {
    import io.github.tgeng.stalker.core.tt.builtins._
    val r = MutableNamespace()
    r.importDefinition(levelType)
    r.importDefinition(universeType)
    r.importDefinition(lsucFn)
    r.importDefinition(lmaxFn)
    r.importDefinition(idType)
    r
  }
}