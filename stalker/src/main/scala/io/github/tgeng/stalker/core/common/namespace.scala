package io.github.tgeng.stalker.core.common

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.common.extraSeqOps
import QualifiedName._
import Error._

trait Namespace extends Iterable[(String, Namespace)]{
  def get(name: String) : Result[Namespace]
  def get(names: Seq[String]) : Result[Namespace] = {
    names.foldLeft[Result[Namespace]]((Right(this)))((ns, n) => ns.flatMap(_.get(n)))
  }

  def qn: QualifiedName
  def isConstructor : Boolean

  def render(qn: QualifiedName): (String, List[String]) = render(qn, Nil) match {
    case head :: rest => (head, rest)
    case _ => throw IllegalArgumentException(s"Invalid qualified name $qn to render.")
  }

  private def render(qn: QualifiedName, current: List[String]) : List[String] = qn match {
    case Root => current
    case parent / name => {
      for ((name1, elem) <- this) {
        if(qn == elem.qn) return name1 :: current
      }
      render(parent, name :: current)
    }
  }
}

trait MutableNamespace extends Namespace {
  def importNs(ns: Namespace) : Unit = ns.qn match {
    case Root => merge(ns)
    case parent / name => this(name) = ns
  }

  def merge(ns: Namespace) : Unit = {
    ns.foreach(this.update)
  }
  
  def addDeclaration(name: String, constructors: String*) : Unit = addDeclaration(name, constructors)

  def addDeclaration(name: String, constructors: Iterable[String]) : Unit = { 
    if (constructors.isEmpty) this(name) = LeafNamespace(qn / name)
    else {
      val ns = InMemoryNamespace(qn / name)
      for (child <- constructors) {
        ns(child) = LeafNamespace(ns.qn / child)
      }
      this(name) = ns
    }
  }

  def update(name: String, ns: Namespace) : Unit
}

object MutableNamespace {
  import io.github.tgeng.stalker.core.tt.builtins._
  import scala.language.implicitConversions
  import io.github.tgeng.stalker.core.tt._

  def createWithBuiltins(qn: QualifiedName) : MutableNamespace = {
    val r = InMemoryNamespace(qn)
    r.importNs(levelType)
    r.importNs(typeType)
    r.importNs(lsucFn)
    r.importNs(lmaxFn)
    r.importNs(idTypeNs)
    r.merge(idTypeNs)
    r
  }
  def create(qn: QualifiedName) : MutableNamespace = InMemoryNamespace(qn)

  given dataToNamespace as Conversion[PreData, Namespace] = d => {
    val r = InMemoryNamespace(d.qn)
    val cons = d.cons
    if (cons != null) {
      for (con <- cons) {
        r(con.name) = LeafNamespace(d.qn / con.name)
      }
    }
    r
  }

  given recordToNamespace as Conversion[PreRecord, Namespace] = r => LeafNamespace(r.qn, false)
  given definitionToNamespace as Conversion[PreDefinition, Namespace] = d => LeafNamespace(d.qn, false)

  val idTypeNs : Namespace = {
    val r = InMemoryNamespace(idType.qn)
    r("Refl") = LeafNamespace(idType.qn / "Refl")
    r
  }
}

private case class InMemoryNamespace(override val qn: QualifiedName) extends MutableNamespace {
  import QualifiedName.{_, given _}
  import scala.collection.mutable.Map
  import scala.collection.mutable.Set
 
  private val content = Map[String, Namespace]()

  override def get(name: String) = content.get(name) match {
    case Some(ns) => Right(ns)
    case None => noNameError(e"Cannot find $name in $qn.")
  }

  override def iterator: Iterator[(String, Namespace)] = content.iterator

  override def update(name: String, ns: Namespace) : Unit = content.update(name, ns)
  
  override def isConstructor = false
}

case class LeafNamespace(override val qn: QualifiedName, override val isConstructor: Boolean = true) extends Namespace {
  override def get(name: String) = noNameError(e"Cannot find $name in $qn.")

  override def iterator: Iterator[(String, Namespace)] = Iterator.empty
}
