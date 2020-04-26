package io.github.tgeng.stalker.core

import scala.util.control.NonLocalReturns._
import Term._
import Whnf._
import Elimination._
import ClauseT._
import Pattern._
import CoPattern._

object reduction {
  def (tms: List[Binding[Term]]).tele(using Γ: Context)(using Σ: Signature) : Result[Telescope] = tms match {
    case Nil => Right(Nil)
    case tm :: rest => for {
      wTm <- tm.ty.whnf
      wRest <- rest.tele
    } yield Binding(wTm)(tm.name) :: wRest
  }
  
  def (tm: Term) whnf(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
    case TWhnf(w) => Right(w)
    case TRedux(fn, elims) => for {
      definition <- Σ getDefinition fn
      rhs <- firstMatch(definition.clauses, elims, definition)
      r <- rhs.whnf
    } yield r
  }

  private def firstMatch(cs: scala.collection.Seq[Clause], e̅: List[Elimination], d: Definition)(using Γ: Context)(using Σ: Signature) : Result[Term] = returning[Result[Term]] {
    for (c <- cs) {
      c match {
        case CheckedClause(_, q̅, v, _) => e̅ / q̅ match {
          case Right(Right(σ)) => throwReturn[Result[Term]](Right(v.subst(σ)))
          case Right(Left(_)) => firstMatch(cs, e̅, d)
          case Left(e) => throwReturn[Result[Term]](Left(e))
        }
      }
    }
    throwReturn[Result[Term]](typingError(s"No matched clause found with eliminators ${e̅}. Is definition ${d.qn} exhaustive?"))
  }
  
  def (v: Term) / (p: Pattern)(using Γ: Context)(using Σ: Signature) : MatchResult = p match {
    case PVar(_) => matched(Substitution.of[Term](v))
    case PRefl | PForced(_) => matched(Substitution.none)
    case PCon(c1, p̅) => v.whnf match {
      case Right(WCon(c2, v̅)) => if(c1 == c2) {
       v̅.map(ETerm(_)) / p̅.map(QPattern(_))
      } else {
        mismatch(v, p)
      }
      case _ => typingError(s"stuck when reducing $v")
    }
    case PForcedCon(_, p̅) => v.whnf match {
      case Right(WCon(_, v̅)) => v̅.map(ETerm(_)) / p̅.map(QPattern(_))
      case _ => typingError(s"stuck when reducing $v")
    }
    case PAbsurd => throw IllegalStateException("Checked pattern should not contain absurd pattern.")
  }
  
  def (e: Elimination) / (q: CoPattern)(using Γ: Context)(using Σ: Signature) : MatchResult = (e, q) match {
    case (ETerm(t), QPattern(p)) => t / p
    case (EProj(π1), QProj(π2)) if π1 == π2 => matched(Substitution.none)
    case _ => mismatch(e, q)
  }
  
  def (e̅: List[Elimination]) / (q̅: List[CoPattern])(using Γ: Context)(using Σ: Signature) : MatchResult = (e̅, q̅) match {
    case (Nil, Nil) => matched(Substitution.none)
    case (e :: e̅, q :: q̅) => for {
      eq <- e / q
      eqs <- eq match {
        // Skip matching if `e / q` already produces a mismatch. 
        case Left(_) => mismatch(e, q)
        case _ => e̅ / q̅
      }
    } yield eq ⊎ eqs
    // This could happen in the following cases
    // * partial application: we simply make it stuck so we don't need to introduce
    //   another syntax for storing partial applications. In practice, one can
    //   compile partial applicable definition into sub functions.
    // * extra arguments: type error indeed
    // * wrong number of args for constructor: type error indeed
    // * mismatched field: this would have resulted an earlier mismatch instead.
    case _ => typingError(s"stuck when matching ${e̅} with ${q̅}")
  }
}