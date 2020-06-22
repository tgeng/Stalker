package io.github.tgeng.common

/** Element of a disjoint-set in the union find algorithm. */
class UnionFindElem[T](val value: T) {
  var parent: UnionFindElem[T] = this
  var rank: Int = 0
  def find : UnionFindElem[T] = if (parent == this) this else {
    val res = parent.find
    parent = res
    res
  }

  override def toString = {
    if (this == parent) {
      s"Root{$value}"
    } else {
      s"Elem{$value ~> ${find.value}}"
    }
  }
}

object UnionFindElem {
  def union[T](elems: Iterable[UnionFindElem[T]]): Unit = {
    val roots = elems.map(_.find).toSet
    roots.maxByOption(_.rank) match {
      case None => return
      case Some(maxRankElem) => { 
        val rest = roots diff Set(maxRankElem)
        rest.foreach(_.parent = maxRankElem)
        rest.maxByOption(_.rank) match {
          case Some(secondMaxRankElem) if (secondMaxRankElem.rank == maxRankElem.rank) => maxRankElem.rank += 1
          case _ => ()
        }
      }
    }
  }
}

object graph {
  import scala.collection.mutable
  import debug._

  /** Detects cycles in a general graph and collect cyclic nodes into groups. 
    * Then returns a topologically sorted seq of such groups and a DAG of such
    * groups, representing the dependencies among them.
    */
  def collapseCycles[T](graph: Map[T, Set[T]]): (Seq[Set[T]], Map[Set[T], Set[Set[T]]]) = {
    val allTs = (graph.keys ++ graph.values.flatten).toSet
    val unionFindElemByT : Map[T, UnionFindElem[T]] = allTs.map{ d => d -> UnionFindElem(d)}.toMap
    val unionFindElemGraph = graph.map{ case (k, v) => (unionFindElemByT(k), v.map(unionFindElemByT(_))) }.toMap
    val visited = mutable.LinkedHashSet[UnionFindElem[T]]()
    val parents = mutable.LinkedHashSet[UnionFindElem[T]]()
    val allUnionFindElems = unionFindElemGraph.keySet | unionFindElemGraph.values.flatten.toSet
    allUnionFindElems.foreach { e =>
      collapseAllLoops(e, unionFindElemGraph, visited, parents)
    }
    val tByRoot = allTs.groupBy(unionFindElemByT(_).find)
    // `visited` stores nodes that the dfs traversal finishes first. Consider
    // graph with the following nodes and edges.
    // 1 -> (2, 3), 2 -> 1
    // Traversal would end with visited populated with (2, 3, 1). After union
    // find it becomes ((1, 2), 3, (1, 2)). Group (1, 2) appeared twice, once
    // for `2` and once for `1`. The first appearance is invalid because when
    // it's added, group (1, 2) is not done yet. Only when the last element (`1`
    // in this case) is processed, we say the group is done. Therefore, we can
    // only say a group is finished when the last node in this group is
    // finished. However, `distinct` always removes latter duplicated elements.
    // Therefore, to make `distinct` honor elements appeared later, we reverse
    // the seq and reverse again.
    val resultSeq = visited.toSeq.reverse.map{_.find}.map{tByRoot(_)}.distinct.reverse
    val resultMap = unionFindElemGraph.groupMap{
      case (k, vs) => tByRoot(k.find)
    }{
      case (k, vs) => {
        // Remove self references
        (vs.map(_.find) diff Set(k.find)).map(tByRoot(_))
      }
    }.map{
      case (k, vs) => (k, vs.flatten.toSet)
    }.filter{
      case (k, vs) => !vs.isEmpty
    }.toMap
    (resultSeq, resultMap)
  }
  
  private def collapseAllLoops[T](
    node: UnionFindElem[T],
    graph: Map[UnionFindElem[T], Set[UnionFindElem[T]]],
    visited: mutable.LinkedHashSet[UnionFindElem[T]],
    parents: mutable.LinkedHashSet[UnionFindElem[T]],
  ) : Unit = {
    if (visited.contains(node)) return
    if (parents.contains(node)) {
      UnionFindElem.union(parents.dropWhile(_ != node))
      return
    }
    parents.add(node)
    if (graph.contains(node)) {
      graph(node).foreach{ collapseAllLoops(_, graph, visited, parents) }
    }
    parents.remove(node)
    visited.add(node)
  }
}
