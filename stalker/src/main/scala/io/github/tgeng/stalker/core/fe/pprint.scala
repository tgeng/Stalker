package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common._
import Block._

trait PPrinter[T] extends BlockConverter[T] {
  final def (t: T) toBlock : Block = t.block(using PriorityContext.zero)

  final def (t: T) block(using parentCtx: PriorityContext) : Block = {
    val thisCtx = t.pctx
    if (parentCtx.priority >= thisCtx.priority) {
      concat("(", t.blockImpl(using PriorityContext.zero), ")")
    } else {
      t.blockImpl(using thisCtx)
    }
  }

  def (t: T) pctx : PriorityContext
  def (t: T) blockImpl : PriorityContext ?=> Block
}

class PriorityContext(val priority: Double)

object PriorityContext {
  val zero = PriorityContext(0)
  val ten = PriorityContext(10)
}

object pprint {
  import FTerm._
  import FElimination._

  given PPrinter[FTerm] {

    override def (t: FTerm) pctx = PriorityContext(t match {
      case _ : FTFunction => 1
      case _ : FTCon => 10
      case _ : FTLevel => 10
      case FTRedux(_, Nil, Nil) => 10
      case FTRedux(_, _, _) => 5
    })

    override def (t: FTerm) blockImpl = t match {
      case FTCon(name, Nil) => oneLineConcat(name, "{", "}")
      case FTCon(name, args) => concat(
        oneLineConcat(name, "{"),
        chopDown(
          args.dropRight(1).map(arg => oneLineConcat(arg.block(using PriorityContext.zero), ",")) :+ args.last.block(using PriorityContext.zero)
        ),
        "}"
      )
      case FTLevel(l) => oneLineConcat(l.toString, "lv")
      case FTRedux(head, names, elims) => oneLine(head) ++ names ++ elims.map(_.block)
      case t => unnestFn(t) match {
        case (bindings, bodyTy) => chopDown(
          bindings.map(b => oneLine(b.block, "->")) :+ bodyTy.block
        )
      }
    }

    private def unnestFn(fn: FTerm) : (List[FBinding], FTerm) = fn match {
      case FTFunction(arg, bodyTy) => unnestFn(bodyTy) match {
        case (args, bodyTy) => (arg :: args, bodyTy)
      }
      case t => (Nil, t)
    }
  }

  given PPrinter[FBinding] {
    override def (b: FBinding) pctx = if (b.name == "") b.ty.pctx else PriorityContext.zero
    override def (b: FBinding) blockImpl = if (b.name == "") b.ty.blockImpl else wrap(b.name, ":", b.ty.block)
  }

  given PPrinter[FElimination] {
    override def (t: FElimination) pctx = t match {
      case FETerm(t) => t.pctx
      case FEProj(p) => PriorityContext.ten
    }

    override def (t: FElimination) blockImpl = t match {
      case FETerm(t) => t.blockImpl
      case FEProj(p) => oneLineConcat(".", p)
    }
  }
}