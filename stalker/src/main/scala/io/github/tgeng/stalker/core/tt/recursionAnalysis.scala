package io.github.tgeng.stalker.core.tt

import scala.collection.mutable

import io.github.tgeng
import tgeng.common._
import tgeng.common.nullOps._
import tgeng.stalker

import stalker.common.QualifiedName

import stalker.core
import core.common.Error._
import core.tt.dependencies.{given _}

case class MutualGroup(
  val declarations: Set[PreDeclaration]
  )(
  val depRecursionGroups: Set[MutualGroup],
  val deps: Set[QualifiedName],
)

object recursionAnalysis {
  def analyzeMutualDependency(decls: Set[PreDeclaration]) : Result[Set[MutualGroup]] = {
    val elemByQn : Map[QualifiedName, UnionFindElem[PreDeclaration]] = decls.map(d => d.qn -> UnionFindElem(d)).toMap

    val graph : Map[UnionFindElem[PreDeclaration], Set[UnionFindElem[PreDeclaration]]] = decls.map{d => 
      elemByQn(d.qn) -> d.deps.filter(elemByQn.contains(_)).map(elemByQn(_))
    }.toMap

    val visited = mutable.Set[UnionFindElem[PreDeclaration]]()
    val parents = mutable.LinkedHashSet[UnionFindElem[PreDeclaration]]()

    graph.keys.foreach{
      collapseAllLoops(_)(using graph, visited, parents, UnionFindElem.union)
    }
    ???
  }

  private def collapseAllLoops[T](node: T)(using
    graph: Map[T, Set[T]],
    visited: mutable.Set[T],
    parents: mutable.LinkedHashSet[T],
    collapse: (Iterable[T]) => Unit
  ) : Unit = {
    if (visited.contains(node)) return
    if (parents.contains(node)) {
      collapse(parents.dropWhile(_ != node))
      return
    }
    parents.add(node)
    graph(node).foreach{ collapseAllLoops(_) }
    parents.remove(node)
    visited.add(node)
  }
}
