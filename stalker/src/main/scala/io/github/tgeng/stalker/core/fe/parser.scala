package io.github.tgeng.stalker.core.fe

import scala.language.postfixOps
import scala.language.implicitConversions
import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

object parser {
  val nameBodyChar = any[Char] & not(anyOf(" \n\r\t()[]{}."))
  val nameHeadChar = nameBodyChar & not(anyOf("'\"`"))
  val name = nameHeadChar +: (nameBodyChar*) & not("->" | ":") withName "<identifier>"
  
}