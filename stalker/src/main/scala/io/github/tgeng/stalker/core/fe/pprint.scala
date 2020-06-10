package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common._
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.LocalNames
import io.github.tgeng.stalker.core.common.Error
import io.github.tgeng.stalker.core.tt._
import io.github.tgeng.stalker.core.fe.tfConversion.{given _, _}
import Block._
import IndentPolicy._
import WrapPolicy._
import DelimitPolicy._

trait PPrinter[T] extends BlockConverter[T] {
  final def (t: T) toBlock : Block = t.block(using PriorityContext.zero)

  def (t: T) block(using parentCtx: PriorityContext) : Block = {
    val thisCtx = t.pctx
    if (parentCtx.priority >= thisCtx.priority) {
      Block()("(", Block(indentPolicy = FixedIncrement(2))(t.blockImpl(using PriorityContext.zero)), ")")
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
  val app = PriorityContext(5)
  val fn = PriorityContext(1)
}

object pprint {
  import FTerm._
  import FElimination._

  given PPrinter[FTerm] {

    override def (t: FTerm) pctx = t match {
      case _ : FTFunction => PriorityContext.fn
      case _ : FTCon => PriorityContext.ten
      case _ : FTLevel => PriorityContext.ten
      case FTRedux(_, Nil, Nil) => PriorityContext.ten
      case FTRedux(_, _, _) => PriorityContext.app
    }

    override def (t: FTerm) blockImpl : PriorityContext ?=> Block = t match {
      case FTCon(name, Nil) => Block(wrapPolicy = NoWrap)(name, "{", "}")
      case FTCon(name, args) => Block()(
        Block(wrapPolicy = NoWrap)(name, "{"),
        Block(wrapPolicy = ChopDown, indentPolicy = FixedIncrement(2), delimitPolicy = Whitespace)(
          args.map(arg => (arg.block(using PriorityContext.app))) : _*
        ),
        "}"
      )
      case FTLevel(l) => Block(wrapPolicy = NoWrap)(l.toString, "lv")
      case FTRedux(head, names, elims) => Block(wrapPolicy = NoWrap, delimitPolicy = Whitespace)(head) ++ names ++ elims.map(_.block(using t.pctx))
      case t => unnestFn(t) match {
        case (bindings, bodyTy) => Block(wrapPolicy = ChopDown, indentPolicy = Aligned, delimitPolicy = Whitespace)(
          bindings.map(b => Block(wrapPolicy = NoWrap, delimitPolicy = Whitespace)(b.block, "->")) :+ bodyTy.block : _*
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
    override def (b: FBinding) blockImpl = if (b.name == "") b.ty.blockImpl else Block(delimitPolicy = Whitespace)(b.name, ":", b.ty.block)
  }

  given PPrinter[FElimination] {
    override def (t: FElimination) block (using PriorityContext) = t match {
      case FETerm(t) => t.block
      case FEProj(p) => Block(wrapPolicy = NoWrap)(".", p)
    }

    override def (t: FElimination) pctx = throw AssertionError("impossible since block is overwritten")

    override def (t: FElimination) blockImpl = throw AssertionError("impossible since block is overwritten")
  }

  def [T](ctx: StringContext) pp (args: Any*)(using LocalNames)(using Namespace): String = {
    val p = ctx.parts.iterator
    val a = args.iterator
    val resultSeq = scala.collection.mutable.ArrayBuffer[Any]()
    resultSeq += p.next
    while(p.hasNext) {
      resultSeq += (a.next match {
        case s: String => s"'$s'"
        case x => x
      })
      resultSeq += p.next
    }
    resultSeq.toBlock.toString
  }

  def (e: Error) toBlock (using LocalNames)(using Namespace): Block = e.localNames match {
    case Some(ln) => e.msg.toBlock(using ln)
    case None => e.msg.toBlock 
  }

  private def (seq: scala.collection.Seq[Any]) toBlock (using LocalNames)(using Namespace): Block = {
    val children = scala.collection.mutable.ArrayBuffer[Block | String]()
    for (part <- seq) {
      part match {
        case s: String => children ++= s.split(" ").asInstanceOf[Array[String]].filter(t => !t.isEmpty)
        case _ => children += Block(wrapPolicy = ChopDown, indentPolicy = FixedIncrement(2))(part.toBlockOrString)
      }
    }
    Block(wrapPolicy = Wrap, delimitPolicy = Paragraph)(children.toSeq : _*)
  }
  
  private def (part: Any) toBlockOrString(using LocalNames)(using Namespace): Block | String = part match {
    case t: Term => t.toFe.toBlock
    case t: Whnf => t.toFe.toBlock
    case t: Elimination => t.toFe.toBlock
    case t: FTerm => t.toBlock
    case t: FElimination => t.toBlock
    case a ∷ b => Block(wrapPolicy = NoWrap, delimitPolicy = Whitespace)(a.toBlockOrString, ":", Block(indentPolicy = Aligned)(b.toBlockOrString))
    case a ≡ b => Block(wrapPolicy = ChopDown, delimitPolicy = Whitespace)(a.toBlockOrString, "=", b.toBlockOrString)
    case e: Error => e.toBlock
    case _ => part.toString
  }
}
