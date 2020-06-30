package io.github.tgeng.stalker.core.tt

import scala.collection.mutable

import io.github.tgeng
import tgeng.common.graph._
import tgeng.common.nullOps._
import tgeng.stalker

import stalker.common.QualifiedName
import stalker.common.Error._

import stalker.core
import core.tt.dependencies.{given _}

case class MutualGroup(
  val declarations: Set[PreDeclaration]
  )(
  val depRecursionGroups: Set[MutualGroup],
  val deps: Set[QualifiedName],
)

object recursionAnalysis {
  def analyzeMutualDependency(decls: Set[PreDeclaration]) : Seq[MutualGroup] = {
    val elemByQn : Map[QualifiedName, PreDeclaration] = decls.map(d => d.qn -> d).toMap

    val graph : Map[PreDeclaration, Set[PreDeclaration]] = decls.map{d => 
      elemByQn(d.qn) -> d.deps.filter(elemByQn.contains(_)).map(elemByQn(_))
    }.toMap

    val (topoSorted, dag) = collapseCycles(graph)
    val mutualGroupByDeclGroup = mutable.Map[Set[PreDeclaration], MutualGroup]()
    topoSorted.map{ declGroup =>
      val mutualGroup = MutualGroup(declGroup)(
        dag.getOrElse(declGroup, Set.empty).map(dep => mutualGroupByDeclGroup(dep)),
        declGroup.flatMap(_.deps) diff elemByQn.keySet)
      mutualGroupByDeclGroup(declGroup) = mutualGroup
      mutualGroup
    }
  }
}