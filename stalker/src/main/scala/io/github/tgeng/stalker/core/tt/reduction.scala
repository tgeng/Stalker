package io.github.tgeng.stalker.core.tt

import scala.util.control.NonLocalReturns._
import io.github.tgeng.common.extraSetOps
import io.github.tgeng.common.debug._
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.Error._
import Term._
import Whnf._
import Elimination._
import Pattern._
import CoPattern._
import utils._

object reduction {
  def (tms: List[Binding[Term]]) toWhnfs(using Γ: Context)(using Σ: Signature) : Result[Telescope] = tms match {
    case Nil => Right(Nil)
    case tm :: rest => for {
      wTm <- tm.ty.toWhnf
      wRest <- rest.toWhnfs
    } yield Binding(wTm)(tm.name) :: wRest
  }
  
  def (tm: Term) toWhnf(using Γ: Context)(using Σ: Signature) : Result[Whnf] = tm match {
    case TWhnf(w) => Right(w)
    case TRedux(fn, elims) => for {
      definition <- Σ getDefinition fn
      rhs <- if (Γ.size == 0 && definition.ct != null) evalCaseTree(definition.ct, Substitution.id, elims)
             else if (definition.clauses != null) evalClauses(definition.clauses, elims, definition.qn)
             else typingErrorWithCtx(e"Cannot reduce definition ${definition.qn} since it's not fully defined.")
      r <- rhs.toWhnf
    } yield r
  } flatMap { _.reduceLevel }

  def (w: Whnf) reduceLevel(using Γ: Context)(using Σ: Signature) : Result[Whnf] = w match {
    case WLMax(lsucs) => {
      var lconst = 0
      var minLsuc = Integer.MAX_VALUE
      (for {
        lsucTuples <- lsucs.liftMap { case LSuc(n, t) => t.toWhnf.map((n, _)) }
        newLsucs = lsucTuples.flatMap{
          case (n, WLConst(l)) => {
            lconst = scala.math.max(lconst, n + l)
            Set()
          }
          case (n, WLMax(lsucs)) => lsucs.map { 
            // Under WLMax, there should only be Whnf of WLConst and WVar.
            // WLMax and any redux should have been processed by calls to toWhnf for each children
            // Any other WHNFs are type errors and should have been caught by type checking before
            // reduction.
            case LSuc(n1, TWhnf(w : WLConst)) => (n + n1, w) 
            case LSuc(n1, TWhnf(w : WVar)) => (n + n1, w) 
            case _ => throw IllegalStateException("At this point there should no longer be any redux under WLMax.")
          }
          case (n, t@WVar(x, Nil)) => Set((n, t))
          case _ => throw IllegalStateException("invalid level term")
        }.flatMap {
          // Do a second round of lconst processing for grand children under child WLMax terms.
          case (n, WLConst(l)) => {
            lconst = scala.math.max(lconst, n + l)
            Set()
          }
          case (n, w) => Set(LSuc(n, TWhnf(w)))
        }.groupBy{
          case LSuc (_, w) => w
        }.values.map{lsucs =>
          val lsuc = lsucs.maxBy{ case LSuc(n, _) => n }
          minLsuc = scala.math.min(minLsuc, lsuc.amount)
          lsuc
        }
      } yield (lconst, newLsucs.toList)) match {
        case Right(0, Nil) => throw IllegalStateException("Encountered empty WLMax.")
        case Right(l, Nil) => Right(WLConst(lconst))
        case Right(0, LSuc(0, t) :: Nil) => t.toWhnf
        case Right(l, lsucs) if l <= minLsuc => Right(WLMax(lsucs.toSet))
        case Right(l, lsucs) => Right(WLMax((LSuc(0, TWhnf(WLConst(l))) :: lsucs).toSet))
        case Left(e) => Left(e)
      }
    }
    case w => Right(w)
  }

  def (l1: Term) <= (l2: Term)(using Γ: Context)(using Σ: Signature) : Result[Boolean] = {
    for maxL1L2 <- lmax(l1, l2).reduceLevel
        l1 <- l1.toWhnf
        l2 <- l2.toWhnf
        r <- if (maxL1L2 == l2 || l1 == WLConst(0)) {
          Right(true)
        } else if (maxL1L2 == l1 || l2 == WLConst(0)) {
          Right(false)
        } else {
          typingErrorWithCtx(e"Cannot determine if $l1 <= $l2.")
        }
    yield r
  }

  private def evalClauses(cs: scala.collection.Seq[CheckedClause], e̅: List[Elimination], qn: QualifiedName)(using Γ: Context)(using Σ: Signature) : Result[Term] = returning[Result[Term]] {
    for (c <- cs) {
      c match {
        case CheckedClause(_, q̅, v, _) => e̅ / q̅ match {
          case Right(Right(σ)) => throwReturn[Result[Term]](Right(v.subst(Substitution.from(σ))))
          case Right(Left(_)) => () // mismatch -> continue
          case Left(e) => throwReturn[Result[Term]](Left(e)) // stuck
        }
      }
    }
    throwReturn[Result[Term]](typingErrorWithCtx(e"No matched clause found with eliminators ${e̅}. Is definition ${qn} exhaustive?"))
  }
  
  def (v: Term) / (p: Pattern)(using Γ: Context)(using Σ: Signature) : MatchResult = p match {
    case PVar(k) => matched(Map(k -> v))
    case PForced(_) => matched(Map.empty)
    case PCon(c1, p̅) => v.toWhnf match {
      case Right(WCon(c2, v̅)) => if(c1 == c2) {
       v̅.map(ETerm(_)) / p̅.map(QPattern(_))
      } else {
        mismatch(v, p)
      }
      case _ => typingErrorWithCtx(e"stuck when reducing $v")
    }
    case PForcedCon(_, p̅) => v.toWhnf match {
      case Right(WCon(_, v̅)) => v̅.map(ETerm(_)) / p̅.map(QPattern(_))
      case _ => typingErrorWithCtx(e"stuck when reducing $v")
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
    case _ => typingErrorWithCtx(e"stuck when matching ${e̅} with ${q̅}")
  }
  def matched(s: Map[Int, Term]) : MatchResult = Right(Right(s))
  private def mismatch(e: Elimination, q: CoPattern) : MatchResult = Right(Left(Mismatch(e, q)))
  private def mismatch(t: Term, p: Pattern) : MatchResult = mismatch(ETerm(t), QPattern(p))
  def (s1e: Either[Mismatch, Map[Int, Term]]) ⊎ (s2e: Either[Mismatch, Map[Int, Term]])(using Γ: Context) : MatchResult = (for {
    s1 <- s1e
    s2 <- s2e
  } yield (s1, s2)) match {
    case Right(s1, s2) => (s1.keySet intersect s2.keySet) match {
      case s if s.forall(k => s1(k) == s2(k)) => matched(s1 ++ s2)
      case _ => typingErrorWithCtx(e"Nonlinear patterns.")
    }
    case Left(l) => Right(Left(l))
  }

  import CaseTree._
  import Elimination._
  import Term._
  import Whnf._

  private def evalCaseTree(Q: CaseTree, σ: Substitution[Term], e̅: List[Elimination])(using Γ: Context)(using Σ: Signature): Result[Term] = {
    (Q, e̅) match {
      case (CTerm(t), _) => t.subst(σ).app(e̅)
      case (CLam(_Q), ETerm(u) :: e̅) => evalCaseTree(_Q, σ ⊎ u, e̅)
      case (CRecord(fields), EProj(π) :: e̅) => evalCaseTree(fields(π), σ, e̅)
      case (CDataCase(x, branches), e̅) => for {
        con <- σ(x).toWhnf
        r <- con match {
          case WCon(c, u̅) => evalCaseTree(branches(c), σ \ x ⊎ u̅, e̅)
          case _ => typingErrorWithCtx(e"Evaluation stuck when trying to perform case match on $con.")
        }
      } yield r
      case (CIdCase(x, τ, _Q), e̅) => for {
        refl <- σ(x).toWhnf
        r <- refl match {
          case WRefl => evalCaseTree(_Q, τ ∘ σ, e̅)
          case _ => typingErrorWithCtx(e"Evaluation stuck when trying to match $refl against Refl.")
        }
      } yield r
      case _ => typingErrorWithCtx(e"Stuck while evaluating case tree $Q with substitution $σ and eliminations ${e̅}")
    }
  }
} 

type MatchResult = Result[Either[Mismatch, Map[Int, Term]]]
case class Mismatch(v: Elimination, p: CoPattern)
