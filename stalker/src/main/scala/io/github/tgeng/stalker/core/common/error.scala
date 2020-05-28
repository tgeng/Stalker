package io.github.tgeng.stalker.core.common


enum Error {
  case TypingError(msg: String)
  case NoNameError(msg: String)
  case DuplicatedDefinitionError(msg: String)

  def msg: String
  val trace: Exception = Exception(msg)
}


object Error {
  type Result = Either[Error, *]

  def typingError(msg: String) = {
    Left(TypingError(msg))
  }

  def noNameError(msg: String) = Left(NoNameError(msg))

  def duplicatedDefinitionError(msg: String) = Left(DuplicatedDefinitionError(msg))

  def assertResult[T](r: Result[T]) : T = r match {
    case Right(r) => r
    case Left(e) => throw e.trace
  }
}
