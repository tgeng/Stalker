package io.github.tgeng.stalker.core.common

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.common.extraSeqOps
import QualifiedName._
import error._

trait Namespace extends Iterable[(String, Namespace)]{
  def get(name: String) : Result[Namespace]
  def get(names: Seq[String]) : Result[Namespace] = {
    names.foldLeft[Result[Namespace]]((Right(this)))((ns, n) => ns.flatMap(_.get(n)))
  }

  def qn: QualifiedName

  def render(qn: QualifiedName): String = render(qn, "")

  private def render(qn: QualifiedName, current: String) : String = qn match {
    case Root => current
    case parent / name => {
      for ((name1, elem) <- this) {
        if(qn == elem.qn) return name1 + current
      }
      render(parent, "." + name + current)
    }
  }
}

class InMemoryNamespace(val qn: QualifiedName) extends Namespace {
  import QualifiedName.{_, given _}
  import scala.language.implicitConversions
  import io.github.tgeng.stalker.core.tt._
  import scala.collection.mutable.Map
 
  private val content = Map[String, Namespace]()

  override def get(name: String) = content.get(name) match {
    case Some(ns) => Right(ns)
    case None => noNameError(s"Cannot find $name in $qn.")
  }

  override def iterator: Iterator[(String, Namespace)] = content.iterator

  def importDefinition(d: PreDefinition) = d.qn match {
    case _ / name => this(name) = d.qn
    case _ => ()
  }

  def update(name: String, qn: QualifiedName): Unit = update(name, InMemoryNamespace.create(qn))
  def update(name: String, ns: Namespace): Unit = content.update(name, ns)
}

object InMemoryNamespace {
  def createWithBuiltins(qn: QualifiedName) = {
    import io.github.tgeng.stalker.core.tt.builtins._
    val r = InMemoryNamespace(qn)
    r.importDefinition(levelType)
    r.importDefinition(universeType)
    r.importDefinition(lsucFn)
    r.importDefinition(lmaxFn)
    r.importDefinition(idType)
    r
  }
  def create(qn: QualifiedName) = InMemoryNamespace(qn)
}