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
  import QualifiedName.{given _}
  import scala.language.implicitConversions
 
  private val content = scala.collection.mutable.Map[String, NamespaceElement[MutableNamespace]]()

  this("Type") = "stalker.builtin.Type"
  this("Nat") = "stalker.builtin.Nat"
  this("String") = "stalker.builtin.String"
  this("Double") = "stalker.builtin.Double"

  override def get(name: String) = content.get(name)

  override def iterator: Iterator[(String, NamespaceElement[Namespace])] = content.iterator

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