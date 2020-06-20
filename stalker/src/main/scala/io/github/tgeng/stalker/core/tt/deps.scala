package io.github.tgeng.stalker.core.tt

import io.github.tgeng.common.nullOps._
import io.github.tgeng.stalker
import stalker.common.QualifiedName

trait Deps[T] {
  def (t: T) deps : Set[QualifiedName]
}

trait TypeDeps[T] {
  def (t: T) typeDeps: Set[QualifiedName]
}

object dependencies {
  import Term._
  import Whnf._
  import Elimination._

  given Deps[Term] {
    def (t: Term) deps = t match {
      case TWhnf(w) => w.deps
      case TRedux(qn, elims) => Set(qn) | elims.toSet.flatMap(_.deps)
    }
  }

  given Deps[Whnf] {
    def (w: Whnf) deps = w match {
      case WFunction(arg, bodyTy) => arg.ty.deps | bodyTy.deps
      case WType(l) => l.deps
      case WLConst(_) => Set.empty
      case WLMax(operands) => operands.toSet.flatMap{_.deps}
      case WLevel => Set.empty
      case WData(qn, params) => Set(qn) | params.toSet.flatMap(_.deps)
      case WRecord(qn, params) => Set(qn) | params.toSet.flatMap(_.deps)
      case WId(level, ty, left, right) => level.deps | ty.deps | left.deps | right.deps
      case WVar(_, _) => Set.empty
      case WCon(_, args) => args.toSet.flatMap(_.deps)
    }
  }

  given Deps[Elimination] {
    def (e: Elimination) deps = e match {
      case ETerm(t) => t.deps
      case EProj(_) => Set.empty
    }
  }

  given Deps[LSuc] {
    def (l: LSuc) deps = l match {
      case LSuc(_, t) => t.deps
    }
  }

  import Pattern._
  import CoPattern._

  given Deps[Pattern] {
    def (p: Pattern) deps = p match {
      case PVar(_) | PAbsurd => Set.empty
      case PCon(_, args) => args.toSet.flatMap(_.deps)
      case PForcedCon(_, args) => args.toSet.flatMap(_.deps)
      case PForced(t) => t.deps
    }
  }

  given Deps[CoPattern] {
    def (q: CoPattern) deps = q match {
      case QPattern(p) => p.deps
      case QProj(_) => Set.empty
    }
  }

  import ClauseT._

  given Deps[PreDeclaration] {
    def (d: PreDeclaration) deps : Set[QualifiedName] = d.typeDeps | (d match {
      case d: PreData => d.cons.!!.toSet.flatMap(_.argTys.toSet.flatMap(_.ty.deps))
      case r: PreRecord => r.fields.!!.toSet.flatMap(_.ty.deps)
      case d: PreDefinition => d.clauses.!!.toSet.flatMap{
        case UncheckedClause(lhs, rhs) => lhs.toSet.flatMap(_.deps) | rhs.deps
      }
    }) 
  }

  given TypeDeps[PreDeclaration] {
    def (d: PreDeclaration) typeDeps : Set[QualifiedName] = d match {
      case d: PreData => d.paramTys.toSet.flatMap(_.ty.deps) | d.ty.deps
      case r: PreRecord => r.paramTys.toSet.flatMap(_.ty.deps) | r.ty.deps
      case d: PreDefinition => d.ty.deps
    }
  }

  import UncheckedRhs._

  given Deps[UncheckedRhs] {
    def (u: UncheckedRhs) deps = u match {
      case UTerm(t) => t.deps
      case UImpossible => Set.empty
    }
  }
}