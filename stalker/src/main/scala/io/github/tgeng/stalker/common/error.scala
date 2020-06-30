package io.github.tgeng.stalker.common

import java.io.File
import io.github.tgeng.parse._
import scala.collection.Seq

enum Error {
  case TypingError(override val msg: Seq[Any], override val localNames: Option[LocalNames])
  case NoNameError(override val msg: Seq[Any])
  case DuplicatedDefinitionError(override val msg: Seq[Any])
  case AmbiguousNameError(override val msg: Seq[Any])
  case ParsingError(e: ParserError[Char])
  case DuplicatedSourceFile(qn: QualifiedName, val sourceFiles: Seq[File])
  case CyclicImport(cycle: Seq[QualifiedName])
  case UnresolvableNamespace(names: List[String])

  def msg: Seq[Any] = Nil
  def localNames: Option[LocalNames] = None
  val trace: Exception = Exception(msg.toString)
}


object Error {
  type Result = Either[Error, *]

  extension resultFilter on [T](r: Result[T]) {
    def withFilter(p : T => Boolean) : Result[T] = r match {
      case Right(t) if (p(t)) => Right(t)
      case Right(t) => throw IllegalStateException(s"You must only do case match for exact matches in for comprehension.")
      case e => e
    }
  }
  def typingError(msg: Seq[Any]) = {
    Left(TypingError(msg, None))
  }

  def typingErrorWithNames(msg: Seq[Any])(using localNames: LocalNames) = Left(TypingError(msg, Some(localNames)))

  def noNameError(msg: Seq[Any]) = Left(NoNameError(msg))

  def duplicatedDefinitionError(msg: Seq[Any]) = Left(DuplicatedDefinitionError(msg))

  def ambiguousNameError(msg: Seq[Any]) = Left(AmbiguousNameError(msg))

  def assertResult[T](r: Result[T]) : T = r match {
    case Right(r) => r
    case Left(e) => throw e.trace
  }

  def [T](ctx: StringContext) e (args: T*): Seq[Any] = {
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
    resultSeq
  }
}
