package io.github.tgeng.stalker.core.common

object error {
  enum Error {
    case TypingError(msg: String)
    case NoNameError(msg: String)
  }
 
  type Result = Either[Error, *]

  import Error._

  def typingError(msg: String) = Left(TypingError(msg))

  def noNameError(msg: String) = Left(NoNameError(msg))
}
