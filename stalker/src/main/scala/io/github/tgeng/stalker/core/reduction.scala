package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import Term._
import Whnf._
import Elimination._

object reduction {
  given termToWhnf as Conversion[Term, Whnf] = (tm: Term) => tm match {
    case TWhnf(w) => w
    case TRedux(fn, elims) => throw UnsupportedOperationException()
  }
  given termsToWhnfs as Conversion[List[Term], List[Whnf]] = (tms: List[Term]) => tms.map(termToWhnf)
}
