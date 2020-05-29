package io.github.tgeng.stalker.core.tt

import scala.util.control.NonLocalReturns._
import io.github.tgeng.common.extraSetOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt.typing.level
import Term._
import Whnf._
import Elimination._
import ClauseT._
import Pattern._
import CoPattern._

object reduction {
  def (tms: List[Binding[Term]]) tele(using Γ: Context)(using Σ: Signature) : Result[Telescope] = tms match {
    case Nil => Right(Nil)
    case tm :: rest => for {
      wTm <- tm.ty.whnf
      wRest <- rest.tele
      _ <- wRest.level
    } yield Binding(wTm)(tm.name) :: wRest
  }
  
  def (tm: Term) whnf(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
    case TWhnf(w) => Right(w)
    case TRedux(fn, elims) => for {
      definition <- Σ getDefinition fn
      rhs <- if (Γ.size == 0 && definition.ct != null) evalCaseTree(definition.ct, Substitution.id, elims)
             else evalClauses(definition.clauses, elims, definition)
      r <- rhs.whnf
      _ <- r.level
    } yield r
  } match {
    case Right(WLevel(l, lsucs)) => for{
      lsucTuples <- lsucs.liftMap { case LSuc(n, t) => t.whnf.map((n, _)) }
      newLsucs = lsucTuples.flatMap{
        case (n, WLevel(l, lsucs)) => lsucs.map{ case LSuc(n1, t) => LSuc(n + n1, t)}
        case (n, t@WVar(x, Nil)) => Set(LSuc(n, TWhnf(t)))
        case _ => throw IllegalStateException("invalid level term")
      }
      newLevel = scala.math.max(lsucTuples.map{
        case (n, WLevel(l, lsucs)) => n + l
        case (n, t@WVar(x, Nil)) => 0
        case _ => throw IllegalStateException("invalid level term")
      }.maxOption.getOrElse(0), l)
    } yield WLevel(newLevel, newLsucs)
    case w => w
  }

  private def evalClauses(cs: scala.collection.Seq[Clause], e̅: List[Elimination], d: Definition)(using Γ: Context)(using Σ: Signature) : Result[Term] = returning[Result[Term]] {
    for (c <- cs) {
      c match {
        case CheckedClause(_, q̅, v, _) => e̅ / q̅ match {
          case Right(Right(σ)) => throwReturn[Result[Term]](Right(v.subst(Substitution.from(σ))))
          case Right(Left(_)) => () // mismatch -> continue
          case Left(e) => throwReturn[Result[Term]](Left(e)) // stuck
        }
      }
    }
    throwReturn[Result[Term]](typingError(e"No matched clause found with eliminators ${e̅}. Is definition ${d.qn} exhaustive?"))
  }
  
  def (v: Term) / (p: Pattern)(using Γ: Context)(using Σ: Signature) : MatchResult = p match {
    case PVar(k) => matched(Map(k -> v))
    case PForced(_) => matched(Map.empty)
    case PCon(c1, p̅) => v.whnf match {
      case Right(WCon(c2, v̅)) => if(c1 == c2) {
       v̅.map(ETerm(_)) / p̅.map(QPattern(_))
      } else {
        mismatch(v, p)
      }
      case _ => typingError(e"stuck when reducing $v")
    }
    case PForcedCon(_, p̅) => v.whnf match {
      case Right(WCon(_, v̅)) => v̅.map(ETerm(_)) / p̅.map(QPattern(_))
      case _ => typingError(e"stuck when reducing $v")
    }
    case PAbsurd => throw IllegalStateException("Checked pattern should not contain absurd pattern.")
  }
  
  private def (e: Elimination) / (q: CoPattern)(using Γ: Context)(using Σ: Signature) : MatchResult = (e, q) match {
    case (ETerm(t), QPattern(p)) => t / p
    case (EProj(π1), QProj(π2)) if π1 == π2 => matched(Map.empty)
    case _ => mismatch(e, q)
  }
  
  private def (e̅: List[Elimination]) / (q̅: List[CoPattern])(using Γ: Context)(using Σ: Signature) : MatchResult = (e̅, q̅) match {
    case (Nil, Nil) => matched(Map.empty)
    case (e :: e̅, q :: q̅) => for {
      eq <- e / q
      eqs <- eq match {
        // Skip matching if `e / q` already produces a mismatch. 
        case Left(_) => mismatch(e, q)
        case _ => e̅ / q̅
      }
      r <- eq ⊎ eqs
    } yield r
    // This could happen in the following cases
    // * partial application: one should not reduce a partial application in the first place.
    // * extra arguments: type error indeed
    // * wrong number of args for constructor: type error indeed
    // * mismatched field: this would have resulted an earlier mismatch instead.
    case _ => typingError(e"stuck when matching ${e̅} with ${q̅}")
  }
  def matched(s: Map[Int, Term]) : MatchResult = Right(Right(s))
  private def mismatch(e: Elimination, q: CoPattern) : MatchResult = Right(Left(Mismatch(e, q)))
  private def mismatch(t: Term, p: Pattern) : MatchResult = mismatch(ETerm(t), QPattern(p))
  def (s1e: Either[Mismatch, Map[Int, Term]]) ⊎ (s2e: Either[Mismatch, Map[Int, Term]]) : MatchResult = (for {
    s1 <- s1e
    s2 <- s2e
  } yield (s1, s2)) match {
    case Right(s1, s2) => (s1.keySet intersect s2.keySet) match {
      case s if s.forall(k => s1(k) == s2(k)) => matched(s1 ++ s2)
      case _ => typingError(e"Nonlinear patterns.")
    }
    case Left(l) => Right(Left(l))
  }

  import CaseTree._
  import Elimination._
  import Term._
  import Whnf._

  private def evalCaseTree(Q: CaseTree, σ: Substitution[Term], e̅: List[Elimination])(using Σ: Signature): Result[Term] = {
    given Context = Context.empty
    (Q, e̅) match {
      case (CTerm(t), _) => t.subst(σ).app(e̅)
      case (CLam(_Q), ETerm(u) :: e̅) => evalCaseTree(_Q, σ ⊎ u, e̅)
      case (CRecord(fields), EProj(π) :: e̅) => evalCaseTree(fields(π), σ, e̅)
      case (CDataCase(x, branches), e̅) => for {
        case WCon(c, u̅) <- σ(x).whnf
        r <- evalCaseTree(branches(c), σ \ x ⊎ u̅, e̅)
      } yield r
      case (CIdCase(x, τ, _Q), e̅) => for {
        case WRefl <- σ(x).whnf
        r <- evalCaseTree(_Q, τ ∘ σ, e̅)
      } yield r
      case _ => typingError(e"Stuck while evaluating case tree $Q with substitution $σ and eliminations ${e̅}")
    }
  }
} 

type MatchResult = Result[Either[Mismatch, Map[Int, Term]]]
case class Mismatch(v: Elimination, p: CoPattern)
