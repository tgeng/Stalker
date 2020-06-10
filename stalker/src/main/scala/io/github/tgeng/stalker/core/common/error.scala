package io.github.tgeng.stalker.core.common

import scala.collection.Seq

enum Error {
  case TypingError(msg: Seq[Any], override val localNames: Option[LocalNames])
  case NoNameError(msg: Seq[Any])
  case DuplicatedDefinitionError(msg: Seq[Any])

  def msg: Seq[Any]
  def localNames: Option[LocalNames] = None
  val trace: Exception = Exception(msg.toString)
}


object Error {
  type Result = Either[Error, *]

  def typingError(msg: Seq[Any]) = {
    Left(TypingError(msg, None))
  }

  def typingErrorWithNames(msg: Seq[Any])(using localNames: LocalNames) = Left(TypingError(msg, Some(localNames)))

  def noNameError(msg: Seq[Any]) = Left(NoNameError(msg))

  def duplicatedDefinitionError(msg: Seq[Any]) = Left(DuplicatedDefinitionError(msg))

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
