package io.github.tgeng.common

extension extraIntOps on (i: Int) {
  def sub: String = i.toString.map(i => ('\u0030' + i).toChar)
}