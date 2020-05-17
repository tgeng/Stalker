package io.github.tgeng.common

import IndentPolicy._
import WrapPolicy._
import DelimitPolicy._

class PrintContext(
  private val sb: StringBuilder,
  private var width: Int,
  private val widthLimit: Int,
  private var indent: Int,
) {
  def widthLeft = widthLimit - width

  def append(s: String) = {
    sb.append(s)
    width += s.size
  }

  def withIndent(indentPolicy: IndentPolicy)(action: => Unit) = {
    val currentIndent = indent
    indent = indentPolicy match {
      case FixedIncrement(n) => indent + n
      case Aligned => width
    }
    for(i <- width until indent) { sb.append(' ') }
    width = indent
    action
    indent = currentIndent
  }

  def newline = {
    sb.append('\n')
    for(i <- 0 until indent) { sb.append(' ') }
    width = indent
  }
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
  def chopDown(blocks: Block*) = Nested(blocks, ChopDown, FixedIncrement(2), Whitespace)
  def chopDownAligned(blocks: Block*) = Nested(blocks, ChopDown, Aligned, Whitespace)
  def wrap(blocks: Block*) = Nested(blocks, Wrap, FixedIncrement(2), Whitespace)
  def flow(blocks: Block*) = Nested(blocks, Wrap, FixedIncrement(0), Whitespace)
  def noWrap(blocks: Block*) = Nested(blocks, NoWrap, Aligned, Concat)
  def exhibit(blocks: Block*) = Nested(blocks, AlwaysNewline, FixedIncrement(2), Concat)
  def display(blocks: Block*) = Nested(blocks, AlwaysNewline, FixedIncrement(0), Concat)

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
      val canFit = width(ctx.widthLeft) >= 0
      var first = true
      if ((canFit || wrapPolicy == NoWrap) && wrapPolicy != AlwaysNewline) {
        for (child <- children) {
          if (!first) {
            delimitPolicy match {
              case Whitespace => ctx.append(" ")
              case Concat => ()
            }
          }
          child.print
          first = false
        }
      } else {
        ctx.withIndent(indentPolicy) {
          wrapPolicy match {
            case Wrap => {
              for (child <- children) {
                if (first && child.width(ctx.widthLeft) < 0 ) {
                  ctx.newline
                }
                first = false
                child.print
                if (child.width(ctx.widthLeft) < 0 ) {
                  ctx.newline
                } else {
                  delimitPolicy match {
                    case Whitespace => ctx.append(" ")
                    case Concat => ()
                  }
                }
              }
            }
            case ChopDown | AlwaysNewline => {
              for (child <- children) {
                if (!first || indentPolicy.isInstanceOf[FixedIncrement]) ctx.newline
                child.print
                first = false
              }
            }
            case NoWrap => throw IllegalStateException()
          }
        }
      }
    }
  }

  private def width(widthLeft: Int) : Int = this match {
    case Atom(s) => if (s.size <= widthLeft) s.size else -1
    case Nested(children, _, _, delimitPolicy) => {
      var width = 0
      var widthLeft2 = widthLeft
      for (child <- children) {
        var childWidth = child.width(widthLeft2)
        if (childWidth < 0) {
          return -1
        } 
        delimitPolicy match {
          case Whitespace => childWidth += 1
          case Concat => ()
        }
        width += childWidth
        widthLeft2 -= childWidth
      }
      delimitPolicy match {
        case Whitespace => width - 1
        case Concat => width
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
