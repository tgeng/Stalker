package io.github.tgeng.stalker.core

import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.common._
import io.github.tgeng.common.extraSetOps
import io.github.tgeng.stalker.common._
import reduction._
import typing.checkTerm
import typing.checkTermsEq
import CaseTree._
import CoPattern._
import Pattern._
import Whnf._
import Term._
import ClauseT._
import UncheckedRhs._

extension elaboration on (p: Problem) {
  def elaborate(using Γ: Context)(using Σ: Signature)(using clauses: ArrayBuffer[Clause]) : Result[CaseTree] = p match {
    // Done
    case ((_E1, Nil) |-> rhs1) :: _ ||| (f, q̅) ∷ _C if _E1.solve.isRight => _E1.solve match {
      case Right(σ) => rhs1 match {
        case UTerm(v) => {
            val vσ = v.subst(σ)
            (vσ ∷ _C).check match {
            case Right(_) => {
              clauses.append(CheckedClause(Γ.toClosedTelescope, q̅, vσ, _C))
              Right(CTerm(vσ))
            }
            case Left(e) => Left(e)
          }
        }
        case _ => typingError("False impossible case.")
      }
      case Left(_) => throw AssertionError()
    }
    // Intro
    case _P ||| (f, q̅) ∷ (_F@WFunction(_A, _B)) => for {
      wA <- _A.whnf 
      r <- withCtxExtendedBy(_F.argName ∷ wA) {
        for {
          wB <- _B.whnf
          _Pmod <- _P.shift(wA)
          r <- (_Pmod ||| (f, q̅.map(_.raise(1)) :+ QPattern(PVar(0))) ∷ wB).elaborate
        } yield CLam(r)
      }
    } yield r
    // Cosplit
    case _P ||| (f, q̅) ∷ (WRecord(qn, v̅)) => for {
      record <- Σ getRecord qn
      fields <- record.getFields
      fieldCaseTrees <- fields.foldLeft[Result[Map[String, CaseTree]]](Right(Map())){ (acc, field) =>
        for {
          m <- acc
          _Pmod <- _P.filter(field.name, fields.map(_.name).toSet)
          wA <- field.ty.substHead(v̅ :+ TRedux(f, q̅.map(_.toElimination))).whnf
          q <- (_Pmod ||| (f, q̅ :+ QProj(field.name)) ∷ wA).elaborate
        } yield m ++ Map(field.name -> q)
      }
    } yield CRecord(fieldCaseTrees)
    case ((_E1, q̅1) |-> rhs1) :: _ ||| (f, q̅) ∷ _C => {
      ???
    }
    case _ => typingError("Elaboration failed.")
  }
}

private def (_E: Set[(Term /? Pattern) ∷ Type]) solve(using Γ: Context)(using Σ: Signature) : Result[Substitution[Term]] = {
  _E.foldLeft(matched(Map.empty)){ case (acc, (w /? p) ∷ _A) =>
    for {
      σ1 <- acc
      σ2 <- w / p
      σ <- σ1 ⊎ σ2
    } yield σ
  }.flatMap {
    case Right(m) => {
      val σ = Substitution.from(m)
      val _ESeq = _E.toList
      val ws = _ESeq.map{ case (w /? _) ∷ _ => w}
      val ps = _ESeq.map{ case (_ /? p) ∷ _ => p}
      val Δ = _ESeq.map{ case (_ /? _) ∷ _A => "" ∷ _A}
      for {
        // Check again to ensure forced patterns are correct.
        _ <- (ps.map(_.toTerm).map(_.subst(σ)) ≡ ws ∷ Δ).check
      } yield σ
    }
    case _ => typingError("Mismatch")
  }
}

private def (_P: UserInput) shift(_A: Type): Result[UserInput] = _P match {
  case Nil => Right(Nil)
  case ((_E, QPattern(p) :: q̅) |-> rhs) :: _P => for {
    _Pmod <- _P.shift(_A)
  } yield ((_E.map{ case (w /? p) ∷ _B => (w.raise(1) /? p) ∷ _B } ++ Set((TWhnf(WVar(0, Nil)) /? p) ∷ _A) , q̅) |-> rhs) :: _Pmod
  case _ => typingError("Unexpected clause")
}

private def (_P: UserInput) filter(fieldName: String, allFieldNames: Set[String]): Result[UserInput] = _P match {
  case Nil => Right(Nil)
  case ((_E, QProj(π) :: q̅) |-> rhs) :: _P => 
    if (allFieldNames.contains(π)) 
      for _Pmod <- _P.filter(fieldName, allFieldNames)
      yield 
        if (fieldName == π) ((_E, q̅) |-> rhs) :: _Pmod
        else _Pmod
    else typingError(s"Unexpected field $π")
  case _ => typingError("Unexpected clause")
}

private def (_P: UserInput) subst(σ: Substitution[Term])(using Σ: Signature): Result[UserInput] = _P match {
  case Nil => Right(Nil)
  case ((_E, q̅) |-> rhs) :: _P => for {
    _Es : Set[Option[Set[(Term /? Pattern) ∷ Type]]] <- _E.liftMap {
      case (w /? p) ∷ _A => for {
        wA <- _A.subst(σ).whnf(using Context.empty)
        r <- ((w.subst(σ) /? p) ∷ wA).simpl
      } yield r
    }
    _Emod = unionAll(_Es)
    _Pmod <- _P.subst(σ)
  } yield _Emod match {
    case Some(_E) => ((_E, q̅) |-> rhs) :: _Pmod
    case None => _Pmod
  }
}


private def (constraint: (Term /? Pattern) ∷ Type) simpl(using Σ: Signature) : Result[Option[Set[(Term /? Pattern) ∷ Type]]] = {
  given Context = Context.empty
  constraint match {
    case (vT /? p) ∷ _A => for {
      v <- vT.whnf
      r <- (v, p, _A) match {
        case (WCon(c, v̅), PCon(c1, p̅), WData(qn, u̅)) => 
          if (c != c1) Right(None)
          else for {
            data <- Σ getData qn
            con <- data(c)
            _Δ <- con.argTys.substHead(u̅).tele
            _E <- ((v̅ /? p̅) ∷ _Δ).simplAll
          } yield _E
        case (WCon(c, v̅), PForcedCon(c1, p̅), WData(qn, u̅)) => 
          if (c != c1) typingError("Mismatched forced constructor")
          else for {
            data <- Σ getData qn
            con <- data(c)
            _Δ <- con.argTys.substHead(u̅).tele
            _E <- ((v̅ /? p̅) ∷ _Δ).simplAll
          } yield _E
        case (WRefl, PRefl, WId(_, _, _)) => Right(Some(Set.empty[(Term /? Pattern) ∷ Type]))
        case _ => Right(Some(Set(constraint)))
      }
    } yield r
  }
}

private def (constraints: (List[Term] /? List[Pattern]) ∷ Telescope) simplAll(using Σ: Signature) : Result[Option[Set[(Term /? Pattern) ∷ Type]]] = {
  given Context = Context.empty
  constraints match {
    case (Nil /? Nil) ∷ Nil => Right(Some(Set.empty))
    case ((v :: v̅) /? (p :: p̅)) ∷ (_A :: _Δ) => for {
      _E1 <- ((v /? p) ∷ _A.ty).simpl
      _Δmod <- _Δ.substHead(v).tele
      _E2 <- ((v̅ /? p̅) ∷ _Δmod).simplAll
    } yield _E1 ∪⊥ _E2
  }
}

private def [T] (a: Option[Set[T]]) ∪⊥ (b: Option[Set[T]]) = (a, b) match {
  case (Some(a), Some(b)) => Some(a union b)
  case _ => None
}

private def unionAll[T](s: Set[Option[Set[T]]]) = s.fold[Option[Set[T]]](Some(Set.empty))(_ ∪⊥ _)

type Problem =  UserInput ||| (QualifiedName, List[CoPattern]) ∷ Type
type UserInput = List[(Set[(Term /? Pattern) ∷ Type], List[CoPattern]) |-> UncheckedRhs]

extension applicationTypingRelation on (app : (QualifiedName, List[CoPattern])) {
  def ∷ (A: Type) = new ∷(app, A)
}

extension userInputBarBarBar on (_P : UserInput) {
  def |||(a: (QualifiedName, List[CoPattern]) ∷ Type) = new |||(_P, a)
}

extension lhsOps on (lhs: (Set[(Term /? Pattern) ∷ Type], List[CoPattern])) {
  def |->(rhs: UncheckedRhs) = new |->(lhs, rhs)
}

extension termMatchingOps on (t: Term) {
  def /?(p: Pattern) = new /?(t, p)
}

extension termsMatchingOps on (ts: List[Term]) {
  def /?(ps: List[Pattern]) = new /?(ts, ps)
}

extension termMatchTypingRelation on (m: Term /? Pattern) {
  def ∷(_A: Type) = new ∷(m, _A)
}

extension termsMatchTypingRelation on (m: List[Term] /? List[Pattern]) {
  def ∷(_Δ: Telescope) = new ∷(m, _Δ)
}

case class |||[A, B](a: A, b: B)
case class |->[Lhs, Rhs](lhs: Lhs, rhs: Rhs)
case class /?[T, P](w: T, p: P)
