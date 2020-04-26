package io.github.tgeng.stalker.core

import scala.collection.Map
import scala.collection.Seq
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.common._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.typing.level
import io.github.tgeng.stalker.core.reduction.tele
import io.github.tgeng.stalker.core.reduction.whnf
import typing.checkElim
import typing.checkTerm

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum DeclarationT[+S <: Status, +C[_], +T] {
  case DataT(val qn: QualifiedName, paramTys: List[Binding[T]], level: Int, cons: C[ConstructorT[T]])
  case RecordT(val qn: QualifiedName, paramTys: List[Binding[T]], level: Int, fields: C[FieldT[T]])
  case DefinitionT(val qn: QualifiedName, ty: T, clauses: C[ClauseT[S, T]], ct: CaseTree | Null)

  def qn: QualifiedName
}

import DeclarationT._

case class ConstructorT[+T](name: String, argTys: List[Binding[T]])

case class FieldT[+T](name: String, ty: T)

enum ClauseT[+S <: Status, +T] {
  case UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs) extends ClauseT[Unchecked, T]
  case CheckedClause(bindings: List[Binding[T]], lhs: List[CoPattern], rhs: Term, ty: T) extends ClauseT[Checked, T]
}

import ClauseT._

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}

import UncheckedRhs._

type SignatureT[+C[_], T] = Map[QualifiedName, DeclarationT[Checked, C, T]]

extension signatureTOps on [C[_], T](Σ: SignatureT[C, T]) {
  def getData(qn: QualifiedName) : Result[DataT[Checked, C, T]] = Σ get qn match {
    case Some(d : DataT[Checked, C, T]) => Right(d.asInstanceOf[DataT[Checked, C, T]])
    case _ => typingError(s"No data schema found for $qn")
  }

  def getRecord(qn: QualifiedName) : Result[RecordT[Checked, C, T]] = Σ get qn match {
    case Some(r : RecordT[Checked, C, T]) => Right(r.asInstanceOf[RecordT[Checked, C, T]])
    case _ => typingError(s"No record schema found for $qn")
  }

  def getDefinition(qn: QualifiedName) : Result[DefinitionT[Checked, C, T]] = Σ get qn match {
    case Some(d : DefinitionT[Checked, C, T]) => Right(d.asInstanceOf[DefinitionT[Checked, C, T]])
    case _ => typingError(s"No definition found for $qn")
  }
}

extension dataTypingOps on (self: Data) {
  def apply(name: String) : Result[Constructor] = self.cons.find(_.name == name) match {
    case Some(c) => Right(c)
    case None => typingError(s"Cannot find constructor '$name' for data ${self.qn}.")
  }
}

extension recordTypingOps on (self: Record) {
  def apply(name: String) : Result[Field] = self.fields.find(_.name == name) match {
    case Some(f) => Right(f)
    case None => typingError(s"Cannot find field '$name' for record ${self.qn}.")
  }
}

type Declaration = DeclarationT[Checked, Seq, Type]
type Data = DataT[Checked, Seq, Type]
type Record = RecordT[Checked, Seq, Type]
type Definition = DefinitionT[Checked, Seq, Type]
type Signature = Map[QualifiedName, Declaration]
type Constructor = ConstructorT[Type]
type Field = FieldT[Type]
type Clause = ClauseT[Checked, Type]

object signatureBuilder {
  type Declaration = DeclarationT[Checked, ArrayBuffer, Type]
  type Data = DataT[Checked, ArrayBuffer, Type]
  type Record = RecordT[Checked, ArrayBuffer, Type]
  type Definition = DefinitionT[Checked, ArrayBuffer, Type]
  type Signature = HashMap[QualifiedName, Declaration]

  type PreDeclaration = DeclarationT[Unchecked, ArrayBuffer, Term] 
  type PreData = DataT[Unchecked, ArrayBuffer, Term]
  type PreRecord = RecordT[Unchecked, ArrayBuffer, Term]
  type PreDefinition = DefinitionT[Unchecked, ArrayBuffer, Term]
  type PreConstructor = ConstructorT[Term]
  type PreField = FieldT[Term]
  type PreUncheckedClause = ClauseT[Unchecked, Term]
  type PreClause = ClauseT[Unchecked, Type]

  import Term._
  import Whnf._
  given Γ as Context = Context.empty

  object Signature {
    def create : Signature = HashMap[QualifiedName, Declaration]()
  }

  extension preDeclarationOps on (self: PreDeclaration) {
    def normalize(using Γ: Context)(using Σ: Signature) : Result[Declaration] = self match {
      case DataT(qn, paramTys, level, cons) => for {
        wParamTys <- paramTys.tele
        wCons <- cons.liftMap(_.normalize(using Γ + wParamTys))
      } yield DataT(qn, wParamTys, level, wCons)
      case r@RecordT(qn, paramTys, level, fields) => for {
        wParamTys <- paramTys.tele
        wFields <- fields.liftMap(_.normalize(using Γ + wParamTys + "self" ∷ r.getSelfType))
      } yield RecordT(qn, wParamTys, level, wFields)
      case DefinitionT(qn, ty, clauses, ct) => for {
        wTy <- ty.whnf
        wClauses <- elaborate
      } yield DefinitionT(qn, wTy, wClauses, ct)
    }
  }
  
  extension recordOps on (self: RecordT[?, ?, ?]) {
    def getSelfType : Type =
      Whnf.WRecord(self.qn, (self.paramTys.size - 1 to 0 by -1).map(i => Term.TWhnf(Whnf.WVar(i, Nil))).toList)
  }
  
  extension preConstructorOps on (self: PreConstructor) {
    def normalize(using Γ: Context)(using Σ: Signature) : Result[Constructor] = for {
      wArgTys <- self.argTys.tele
    } yield ConstructorT(self.name, wArgTys)
  }
  
  extension preFieldsOps on (self: PreField) {
    def normalize(using Γ: Context)(using Σ: Signature) : Result[Field] = for {
      wTy <- self.ty.whnf
    } yield FieldT(self.name, wTy)
  }
  
  extension preUncheckedClauseOps on (self: PreUncheckedClause) {
    def normalize(using Γ: Context)(using Σ: Signature): Result[PreClause] = self match {
      case UncheckedClause(lhs, rhs) => Right(UncheckedClause(lhs, rhs))
      // case CheckedClause(bindings, lhs, rhs, ty) => for {
      //   wBindings <- bindings.liftMap(b => b.ty.whnf.map(Binding(_)(b.name)))
      //   wTy <- ty.whnf
      // } yield CheckedClause(wBindings, lhs, rhs, wTy)
    }
  }

  extension signatureOps on (Σ: Signature) {

    def += (d: PreDeclaration) : Result[Unit] = {
      given Signature = Σ
      for {
        wD <- d.normalize
        _ <- wD match {
          case d : Data => d.paramTys.level
          case r : Record => r.paramTys.level
          case d : Definition => d.ty.level
        }
      } yield Σ(d.qn) = wD
    } 

    def += (qn: QualifiedName, c: PreConstructor) : Result[Unit] = {
      given s as Signature = Σ
      for {
        data <- Σ getData qn
        wC <- c.normalize
        cL <- wC.argTys.level(using Γ + data.paramTys)
        _ <- cL <= data.level match {
          case true => Right(())
          case _ => typingError(s"Level of arguments in constructor $c is above that of data declaration $qn.")
        }
      } yield { data.cons.append(wC); () }
    }

    def += (qn: QualifiedName, f: PreField) : Result[Unit] = {
      given s as Signature = Σ
      for {
        record <- Σ getRecord qn
        wF <- f.normalize
        cL <- wF.ty.level(using Γ + record.paramTys + "self" ∷ record.getSelfType)
        _ <- cL <= record.level match {
          case true => Right(())
          case _ => typingError(s"Level of field $f is above that of record declaration $qn.")
        }
      } yield { record.fields.append(wF); () }
    }

    def +=(qn: QualifiedName, c: Clause) : Result[Unit] ={
      given s as Signature = Σ
      c match {
        case CheckedClause(_Δ, q̅, v, _B) => for {
          definition <- Σ getDefinition qn
          _ <- _Δ.level
          _ <- (TRedux(qn, Nil) ∷ definition.ty |- q̅.map(_.toElimination) ∷ _B).check(using Γ + _Δ)
          _ <- (v ∷ _B).check(using Γ + _Δ)
        } yield { definition.clauses.append(c); ()}
      }
    }
  }
}