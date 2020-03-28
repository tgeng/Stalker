package io.github.tgeng.stalker.core

import scala.language.implicitConversions
import Term._
import Whnf._
import Elimination._

object reduction {
  given termToWhnf(using Γ: Context)(using Σ: Signature) as Conversion[Term, Whnf] = (tm: Term) => reduce(tm)
  given termsToWhnfs(using Γ: Context)(using Σ: Signature) as Conversion[List[Term], List[Whnf]] = (tms: List[Term]) => tms.map(termToWhnf)
}

def reduce(tm: Term)(using Γ: Context)(using Σ: Signature) = tm match {
  case TWhnf(w) => w
  case TRedux(fn, elims) => throw UnsupportedOperationException()
}