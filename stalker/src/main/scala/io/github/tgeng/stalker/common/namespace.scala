package io.github.tgeng.stalker.common

import scala.collection.Set
import scala.collection.Map
import scala.collection.mutable
import scala.collection.immutable
import nsElemSetOps._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.common.extraSetOps
import Error._


enum NsElem {
  case NNamespace(ns: Namespace)
  case NQualifiedName(qn: QualifiedName)
}

import NsElem._

trait Namespace {
  def resolve(names: String*) : Result[Set[NsElem]] = resolve(names)
  def resolve(names: Iterable[String]): Result[Set[NsElem]] = resolveImpl(names.toList)
  def resolveImpl(names: List[String]): Result[Set[NsElem]]
  def render(qn: QualifiedName): List[String] = {
    val qnParts = qn.parts.reverse
      renderImpl(qn) match {
      case Left(names) => names
      case Right(_) => qnParts
    }
  }
  protected def renderImpl(qn: QualifiedName): Either[List[String], Unit]
}

extension nsElemSetOps on (elems: Set[NsElem]) {
  def namespaces: Set[Namespace] = elems.collect{ case NNamespace(ns) => ns }
  def qualifiedNames : Set[QualifiedName] = elems.collect { case NQualifiedName(qn) => qn }
}

extension nsElemMutableSetOps on (elems: mutable.Set[NsElem]) {
  def addNs(ns: Namespace) = elems.add(NNamespace(ns))
  def addQn(qn: QualifiedName) = elems.add(NQualifiedName(qn))
}

trait MemNamespace[NS <: MemNamespace[NS, S, M], S <: Set, M <: Map](
  val rootElems: S[NsElem],
  val subspaces: M[String, NS]) extends Namespace {
  override def resolve(names: Iterable[String]): Result[Set[NsElem]] = resolveImpl(names.toList)
  override def resolveImpl(names: List[String]): Result[Set[NsElem]] = names match {
    case Nil => Right(rootElems)
    case name :: rest => for {
      elemsFromThis : Set[NsElem] <- subspaces.get(name) match {
        case Some(ns) => {
          ns.resolveImpl(rest)
        }
        case None => Right(Set.empty)
      }
      siblingNamespaces : Set[Namespace] = rootElems.collect{case NNamespace(n) => n}
      elemsFromSiblings : Set[Set[NsElem]] <- siblingNamespaces.liftMap{_.resolveImpl(names)}
    } yield elemsFromThis | elemsFromSiblings.flatten
  }

  override def renderImpl(qn: QualifiedName): Either[List[String], Unit] = for {
    _ <- rootElems.qualifiedNames.contains(qn) match {
      case true => Left(Nil)
      case false => Right(())
    }
    _ <- subspaces.toSeq.liftMap {
      case (name, ns) => ns.renderImpl(qn).left.map{ name :: _ }
    }
  } yield ()
}

class MutableNamespace(
    startSet : mutable.Set[NsElem] = mutable.Set[NsElem](),
    startElems : mutable.Map[String, MutableNamespace] = mutable.Map[String, MutableNamespace]()
  ) extends MemNamespace[MutableNamespace, mutable.Set, mutable.Map](
  startSet,
  startElems) {
  def apply(names: String*) : mutable.Set[NsElem] = applyImpl(names.toList)
  def apply(names: Iterable[String]) : mutable.Set[NsElem] = applyImpl(names.toList)
  private def applyImpl(names: List[String]) : mutable.Set[NsElem] = names match {
    case Nil => rootElems
    case name :: rest => subspaces.getOrElseUpdate(name, emptyMutableNamespace).applyImpl(rest)
  }


  def seal : ImmutableNamespace = {
    import scala.language.implicitConversions
    ImmutableNamespace(
      rootElems.to(immutable.Set),
      subspaces.view.mapValues{_.seal}.to(immutable.Map))
  }

  override def toString = s"MutableNamespace{$startSet, $startElems}"
}

// workaround type inference failure. Inline this definition to see the problem.
private def emptyMutableNamespace : MutableNamespace = new MutableNamespace()

case class ImmutableNamespace(
  override val rootElems: immutable.Set[NsElem],
  override val subspaces: immutable.Map[String, ImmutableNamespace]
) extends MemNamespace[ImmutableNamespace, immutable.Set, immutable.Map](rootElems, subspaces)