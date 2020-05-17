package io.github.tgeng.common

import IndentPolicy._
import WrapPolicy._
import DelimitPolicy._

class PrintContext(
  val sb: StringBuilder,
  private var width: Int,
  private val widthLimit: Int,
  private var indent: Int,
) {
  def widthLeft = widthLimit - width

  def append(s: String) = {
    if (width < indent) {
      for(_ <- width until indent) { 
        sb.append(' ') 
      }
      width = indent
    }
    sb.append(s)
    width += s.size
  }

  def withIndent(indentPolicy: IndentPolicy)(action: => Unit) = {
    val currentIndent = indent
    indent = indentPolicy match {
      case FixedIncrement(n) => indent + n
      case Aligned => scala.math.max(width, indent)
    }
    action
    indent = currentIndent
  }

  def delimitWithNewline = {
    sb.lastOption match {
      case Some(c) if !c.isWhitespace => {
        sb.append('\n')
        width = 0
      }
      case _ => ()
    }
  }

  def delimitWithSpace = {
    sb.lastOption match {
      case Some(c) if !c.isWhitespace => {
        sb.append(' ')
        width += 1
      }
      case _ => ()
    }
  }

  def newlineSaving = scala.math.min(indent - width, 0)
}

object PrintContext {
  def from(sb: StringBuilder, widthLimit : Int = 100) = {
    val lineStart = sb.lastIndexOf('\n') + 1
    val width = sb.length - lineStart
    var indent = 0
    var i = lineStart
    while(i < sb.length && sb.charAt(i) == ' ') {
      indent += 1
      i += 1
    }
    PrintContext(sb, width, widthLimit, indent)
  }
}

object Block {
  def flow(blocks: Block*) = Nested(blocks, Wrap, FixedIncrement(0), Whitespace)
  def wrap(blocks: Block*) = Nested(blocks, Wrap, FixedIncrement(2), Whitespace)
  def chopDown(blocks: Block*) = Nested(blocks, ChopDown, FixedIncrement(2), Whitespace)
  def chopDownAligned(blocks: Block*) = Nested(blocks, ChopDown, Aligned, Whitespace)
  def concat(blocks: Block*) = Nested(blocks, NoWrap, Aligned, Concat)
  def oneLine(blocks: Block*) = Nested(blocks, NoWrap, Aligned, Whitespace)
  def multiLine(blocks: Block*) = Nested(blocks, AlwaysNewline, FixedIncrement(0), Concat)
  def exhibit(blocks: Block*) = Nested(blocks, AlwaysNewline, FixedIncrement(2), Concat)

  given Conversion[String, Block] = Atom(_)
}

enum Block {
  case Atom(s: String)
  case Nested(
    children: Seq[Block],
    wrapPolicy: WrapPolicy,
    indentIncrement: IndentPolicy,
    delimitPolicy: DelimitPolicy,
  )

  def print(sb: StringBuilder, widthLimit: Int = 100) : Unit = print(using PrintContext.from(sb, widthLimit))

  def print(using ctx: PrintContext) : Unit = this match {
    case Atom(s) => ctx.append(s)
    case Nested(children, wrapPolicy, indentPolicy, delimitPolicy) => {
      ctx.withIndent(indentPolicy) {
        val canFit = !width(ctx.widthLeft).isEmpty
        var first = true
        if ((canFit || wrapPolicy == NoWrap) && wrapPolicy != AlwaysNewline) {
          for (child <- children) {
            if (!first) {
              delimitPolicy match {
                case Whitespace => ctx.delimitWithSpace
                case Concat => ()
              }
            }
            child.print
            first = false
          }
        } else {
          wrapPolicy match {
            case Wrap => {
              for (child <- children) {
                if (child.width(ctx.widthLeft).isEmpty) {
                  ctx.delimitWithNewline
                } else {
                  delimitPolicy match {
                    case Whitespace => ctx.delimitWithSpace
                    case Concat => ()
                  }
                }
                child.print
              }
            }
            case ChopDown | AlwaysNewline => {
              for (child <- children) {
                if (!first || indentPolicy.isInstanceOf[FixedIncrement]) ctx.delimitWithNewline
                first = false
                child.print
              }
              if (indentPolicy.isInstanceOf[FixedIncrement]) ctx.delimitWithNewline
            }
            case NoWrap => throw IllegalStateException()
          }
        }
      }
    }
  }

  private def width(widthLeft: Int)(using ctx: PrintContext) : Option[Int] = this match {
    case Atom(s) => if (s.size <= widthLeft) Some(s.size) else None
    case Nested(children, wrapPolicy, indentPolicy, delimitPolicy) => {
      wrapPolicy match {
        case AlwaysNewline => return None
        case _ => ()
      }
      var width = 0
      var widthLeft2 = widthLeft
      for (child <- children) {
        var childWidth = child.width(widthLeft2) match {
          case Some(w) => w
          case None => return None
        }
        delimitPolicy match {
          case Whitespace => childWidth += 1
          case Concat => ()
        }
        width += childWidth
        widthLeft2 -= childWidth
      }
      delimitPolicy match {
        case Whitespace => Some(width - 1)
        case Concat => Some(width)
      }
    }
  }
}

enum WrapPolicy {
  case NoWrap
  case Wrap
  case ChopDown
  case AlwaysNewline
}

enum IndentPolicy {
  case FixedIncrement(amount: Int)
  case Aligned
}

enum DelimitPolicy {
  case Concat
  case Whitespace
}
