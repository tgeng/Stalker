package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.LocalNames
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt._

trait TF[T, F] {
  def (t: T) toFe(using localVars: LocalNames)(using ns: Namespace) : F
}

object tfConversion {
  import Term._
  import FTerm._
  import Whnf._
  import FElimination._
  import Elimination._
  import builtins._

  given TF[Term, FTerm] {
    def (t: Term) toFe(using localVars: LocalNames)(using ns: Namespace) : FTerm = t match {
      case TWhnf(w) => w.toFe
      case TRedux(qn, elims) => ftRedux(qn, elims.map(_.toFe))
    }
  }

  given TF[Whnf, FTerm] {
    def (w: Whnf) toFe(using localVars: LocalNames)(using ns: Namespace) : FTerm = w match {
      case WFunction(arg, bodyTy) => FTFunction(arg.toFe, localVars.withName(arg.name) { bodyTy.toFe })
      case WType(level) => ftRedux(typeType.qn, FETerm(level.toFe))
      case WLConst(l) => FTLevel(l)
      case WLMax(ops) => ops.toList.sortBy(_.toString) match {
        case Nil => throw IllegalStateException("Encountered invalid empty WLMax term.")
        case first :: rest => maxFeImpl(first, rest)
      }
      case WLevel => ftRedux(levelType.qn)
      case WData(qn, params) => ftRedux(qn, params.map(t => FETerm(t.toFe)))
      case WRecord(qn, params) => ftRedux(qn, params.map(t => FETerm(t.toFe)))
      case WId(l, ty, x, y) => ftRedux(idType.qn, FETerm(l.toFe), FETerm(ty.toFe), FETerm(x.toFe), FETerm(y.toFe))
      case WVar(idx, elims) => FTRedux(localVars.get(idx), Nil, elims.map(_.toFe))
      case WCon(con, args) => FTCon(con, args.map(_.toFe))
    }
  }

  private def maxFeImpl(first: LSuc, rest: List[LSuc])(using localVars: LocalNames)(using ns: Namespace) : FTerm = rest.foldRight(sucFeImpl(first))((e, acc) => ftRedux(lmaxFn.qn, FETerm(sucFeImpl(e)), FETerm(acc)))
  private def sucFeImpl(lsuc: LSuc)(using localVars: LocalNames)(using ns: Namespace) : FTerm = lsuc match {
    case LSuc(l, t) => sucFeImpl(l, t.toFe)
  }
  private def sucFeImpl(l: Int, t: FTerm)(using localVars: LocalNames)(using ns: Namespace) : FTerm = (0 until l).foldLeft(t)((acc, _) => ftRedux(lsucFn.qn, FETerm(acc)))

  given TF[Elimination, FElimination] {
    def (w: Elimination) toFe(using localVars: LocalNames)(using ns: Namespace) : FElimination = w match {
      case ETerm(t) => FETerm(t.toFe)
      case EProj(p) => FEProj(p)
    }
  }

  given TF[Binding[Term], FBinding] {
    def (b: Binding[Term]) toFe(using localVars: LocalNames)(using ns: Namespace) : FBinding = FBinding(b.name, b.ty.toFe)
  }

  private def ftRedux(qn: QualifiedName, elims: List[FElimination])(using ns: Namespace) : FTerm = ns.render(qn) match {
    case (head, names) => FTRedux(head, names, elims)
  }

  private def ftRedux(qn: QualifiedName, elims: FElimination*)(using ns: Namespace) : FTerm = ns.render(qn) match {
    case (head, names) => FTRedux(head, names, elims.toList)
  }
}
