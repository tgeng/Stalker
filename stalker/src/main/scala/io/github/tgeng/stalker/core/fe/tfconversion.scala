package io.github.tgeng.stalker.core.fe

import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt._

trait TF[T, F] {
  def (t: T) toFe(using ns: Namespace) : F = t.toFeImpl(using LocalNames())

  def (t: T) toFeImpl(using localVars: LocalNames)(using ns: Namespace) : F
}

object tfConversion {
  import Term._
  import FTerm._
  import Whnf._
  import FElimination._
  import Elimination._
  import builtins._

  given TF[Term, FTerm] {
    def (t: Term) toFeImpl(using localVars: LocalNames)(using ns: Namespace) : FTerm = t match {
      case TWhnf(w) => w.toFeImpl
      case TRedux(qn, elims) => ftRedux(qn, elims.map(_.toFeImpl))
    }
  }

  given TF[Whnf, FTerm] {
    def (w: Whnf) toFeImpl(using localVars: LocalNames)(using ns: Namespace) : FTerm = w match {
      case WFunction(arg, bodyTy) => FTFunction(arg.toFeImpl, localVars.withName(arg.name) { bodyTy.toFeImpl })
      case WType(level) => ftRedux(universeType.qn, FETerm(level.toFeImpl))
      case WLevel(l, maxOperands) => (l, maxOperands.toList) match {
        case (l, Nil) => FTLevel(l)
        case (l, lsuc :: rest) => sucFeImpl(l, maxFeImpl(lsuc, rest))
      }
      case WLevelType => ftRedux(levelType.qn)
      case WData(qn, params) => ftRedux(qn, params.map(t => FETerm(t.toFeImpl)))
      case WRecord(qn, params) => ftRedux(qn, params.map(t => FETerm(t.toFeImpl)))
      case WId(l, ty, x, y) => ftRedux(idType.qn, FETerm(l.toFeImpl), FETerm(ty.toFeImpl), FETerm(x.toFeImpl), FETerm(y.toFeImpl))
      case WVar(idx, elims) => FTRedux(localVars.get(idx), Nil, elims.map(_.toFeImpl))
      case WCon(con, args) => FTCon(con, args.map(_.toFeImpl))
    }
  }

  private def maxFeImpl(first: LSuc, rest: List[LSuc])(using localVars: LocalNames)(using ns: Namespace) : FTerm = rest.foldRight(sucFeImpl(first))((e, acc) => ftRedux(lmaxFn.qn, FETerm(sucFeImpl(e)), FETerm(acc)))
  private def sucFeImpl(lsuc: LSuc)(using localVars: LocalNames)(using ns: Namespace) : FTerm = lsuc match {
    case LSuc(l, t) => sucFeImpl(l, t.toFeImpl)
  }
  private def sucFeImpl(l: Int, t: FTerm)(using localVars: LocalNames)(using ns: Namespace) : FTerm = (0 until l).foldLeft(t)((acc, _) => ftRedux(lsucFn.qn, FETerm(acc)))

  given TF[Elimination, FElimination] {
    def (w: Elimination) toFeImpl(using localVars: LocalNames)(using ns: Namespace) : FElimination = w match {
      case ETerm(t) => FETerm(t.toFeImpl)
      case EProj(p) => FEProj(p)
    }
  }

  given TF[Binding[Term], FBinding] {
    def (b: Binding[Term]) toFeImpl(using localVars: LocalNames)(using ns: Namespace) : FBinding = FBinding(b.name, b.ty.toFeImpl)
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