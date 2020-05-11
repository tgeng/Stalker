package io.github.tgeng.common

extension extraIntOps on (i: Int) {
  def sub: String = i.toString.map(i => (i - '0' + '₀').toChar)
}