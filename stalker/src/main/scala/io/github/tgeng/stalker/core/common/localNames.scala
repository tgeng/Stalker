package io.github.tgeng.stalker.core.common

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._

class LocalNames(val names: ArrayBuffer[String] = ArrayBuffer[String]()) {

  def get(idx: Int) : String = {
    if (names.isEmpty) {
      Exception().printStackTrace
    }
    names(idx)
  }
  def add(name: String) = names.prepend(name)
  def withName[T](name: String)(action: => T) : T = {
    names.prepend(name)
    val r = action
    names.dropInPlace(1)
    r
  }

  override def toString = names.toString
}