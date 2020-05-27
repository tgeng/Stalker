package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt._

trait TF[T, F] {
  def (t: T) fe(using ns: Namespace) : F = t.feImpl(using LocalNames())

  def (t: T) feImpl(using localVars: LocalNames)(using ns: Namespace) : F
}

object tfConversion {
  import Term._
  import FTerm._
  import Whnf._
  import FElimination._
  import Elimination._
  import builtins._

  given TF[Term, FTerm] {
    def (t: Term) feImpl(using localVars: LocalNames)(using ns: Namespace) : FTerm = t match {
      case TWhnf(w) => w.feImpl
      case TRedux(qn, elims) => ftRedux(qn, elims.map(_.feImpl))
    }
  }

  given TF[Whnf, FTerm] {
    def (w: Whnf) feImpl(using localVars: LocalNames)(using ns: Namespace) : FTerm = w match {
      case WFunction(arg, bodyTy) => FTFunction(arg.feImpl, localVars.withName(arg.name) { bodyTy.feImpl })
      case WUniverse(level) => ftRedux(universeType.qn, FETerm(level.feImpl))
      case WLevel(l, maxOperands) => (l, maxOperands.toList) match {
        case (l, Nil) => FTLevel(l)
        case (l, lsuc :: rest) => sucFeImpl(l, maxFeImpl(lsuc, rest))
      }
      case WLevelType => ftRedux(levelType.qn)
      case WData(qn, params) => ftRedux(qn, params.map(t => FETerm(t.feImpl)))
      case WRecord(qn, params) => ftRedux(qn, params.map(t => FETerm(t.feImpl)))
      case WId(l, ty, x, y) => ftRedux(idType.qn, FETerm(l.feImpl), FETerm(ty.feImpl), FETerm(x.feImpl), FETerm(y.feImpl))
      case WVar(idx, elims) => FTRedux(localVars.get(idx), Nil, elims.map(_.feImpl))
      case WCon(con, args) => FTCon(con, args.map(_.feImpl))
    }
  }

  private def maxFeImpl(first: LSuc, rest: List[LSuc])(using localVars: LocalNames)(using ns: Namespace) : FTerm = rest.foldRight(sucFeImpl(first))((e, acc) => ftRedux(lmaxFn.qn, FETerm(sucFeImpl(e)), FETerm(acc)))
  private def sucFeImpl(lsuc: LSuc)(using localVars: LocalNames)(using ns: Namespace) : FTerm = lsuc match {
    case LSuc(l, t) => sucFeImpl(l, t.feImpl)
  }
  private def sucFeImpl(l: Int, t: FTerm)(using localVars: LocalNames)(using ns: Namespace) : FTerm = (0 until l).foldLeft(t)((acc, _) => ftRedux(lsucFn.qn, FETerm(acc)))

  given TF[Elimination, FElimination] {
    def (w: Elimination) feImpl(using localVars: LocalNames)(using ns: Namespace) : FElimination = w match {
      case _ => ???
    }
  }

  given TF[Binding[Term], FBinding] {
    def (b: Binding[Term]) feImpl(using localVars: LocalNames)(using ns: Namespace) : FBinding = FBinding(b.name, b.ty.feImpl)
  }

  private def ftRedux(qn: QualifiedName, elims: List[FElimination])(using ns: Namespace) : FTerm = ns.render(qn) match {
    case (head, names) => FTRedux(head, names, elims)
  }

  private def ftRedux(qn: QualifiedName, elims: FElimination*)(using ns: Namespace) : FTerm = ns.render(qn) match {
    case (head, names) => FTRedux(head, names, elims.toList)
  }
}

class LocalNames {
  import scala.collection.mutable.ArrayBuffer

  val names = ArrayBuffer[String]()

  def get(idx: Int) : String = names(idx)
  def withName[T](name: String)(action: => T) : T = {
    names.prepend(name)
    val r = action
    names.dropInPlace(1)
    r
  }
}