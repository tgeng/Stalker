package io.github.tgeng.stalker.core

import scala.collection.Map
import scala.collection.Seq
import scala.collection.mutable.HashMap
import io.github.tgeng.common._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.typing.level
import io.github.tgeng.stalker.core.reduction.tele
import io.github.tgeng.stalker.core.reduction.whnf
import typing.checkElim
import typing.checkTerm
import stringBindingOps._

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum DeclarationT[+S <: Status, +T] {
  case DataT(val qn: QualifiedName)(val paramTys: List[Binding[T]], val level: Int, val cons: Seq[ConstructorT[T]] | Null)
  case RecordT(val qn: QualifiedName)(val paramTys: List[Binding[T]], val level: Int, val fields: Seq[FieldT[T]] | Null)
  case DefinitionT(val qn: QualifiedName)(val ty: T, val clauses: Seq[ClauseT[S, T]], val ct: CaseTree | Null)

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

class Signature(val content: Map[QualifiedName, DeclarationT[Checked, Type]]) {
  def getData(qn: QualifiedName) : Result[DataT[Checked, Type]] = content get qn match {
    case Some(d : DataT[Checked, Type]) => Right(d.asInstanceOf[DataT[Checked, Type]])
    case _ => typingError(s"No data schema found for $qn")
  }

  def getRecord(qn: QualifiedName) : Result[RecordT[Checked, Type]] = content get qn match {
    case Some(r : RecordT[Checked, Type]) => Right(r.asInstanceOf[RecordT[Checked, Type]])
    case _ => typingError(s"No record schema found for $qn")
  }

  def getDefinition(qn: QualifiedName) : Result[DefinitionT[Checked, Type]] = content get qn match {
    case Some(d : DefinitionT[Checked, Type]) => Right(d.asInstanceOf[DefinitionT[Checked, Type]])
    case _ => typingError(s"No definition found for $qn")
  }

}

type Declaration = DeclarationT[Checked, Type]
type Data = DataT[Checked, Type]
type Record = RecordT[Checked, Type]
type Definition = DefinitionT[Checked, Type]
type Constructor = ConstructorT[Type]
type Field = FieldT[Type]
type Clause = ClauseT[Checked, Type]

extension dataTypingOps on (self: Data) {
  def apply(name: String) : Result[Constructor] = self.getCons.flatMap {
    _.find(_.name == name) match {
      case Some(c) => Right(c)
      case None => typingError(s"Cannot find constructor '$name' for data ${self.qn}.")
    }
  } 

  def getCons : Result[Seq[Constructor]] = {
    val cons = self.cons
    if (cons == null) return typingError(s"Record ${self.qn} is declared but not initialized.")
    Right(cons)
  }
}

extension recordTypingOps on (self: Record) {
  def apply(name: String) : Result[Field] = self.getFields.flatMap {
    _.find(_.name == name) match {
    case Some(f) => Right(f) 
    case None => typingError(s"Cannot find field '$name' for record ${self.qn}.") 
    } 
  }

  def getFields : Result[Seq[Field]] = {
    val fields = self.fields
    if (fields == null) return typingError(s"Record ${self.qn} is declared but not initialized.")
    Right(fields)
  }
}

type PreDeclaration = DeclarationT[Unchecked, Term]
type PreConstructor = ConstructorT[Term]
type PreField = FieldT[Term]

class SignatureBuilder(val mContent: HashMap[QualifiedName, DeclarationT[Checked, Type]]) extends Signature(mContent) {
  given Signature = this
  given Context = Context.empty

  def += (d: PreDeclaration) : Unit = {
    d match {
      case d@DataT(qn) => for {
        _Δ <- d.paramTys.tele
        level <- _Δ.level
        cons <- d.cons match {
          case _ : Null => Right(null)
          case cons : Seq[PreConstructor] => cons.reduceCons(using Context.empty + _Δ)
        }
      } yield mContent(qn) = DataT(qn)(_Δ, level, cons)
      case r@RecordT(qn) => for {
        _Δ <- r.paramTys.tele
        level <- _Δ.level
        fields <- r.fields match {
          case _ : Null => Right(null)
          case fields: Seq[PreField] => fields.reduceFields(using Context.empty + _Δ + ("self" ∷ Whnf.WRecord(qn, _Δ.vars.toList)))
        }
      } yield mContent(qn) = RecordT(qn)(_Δ, level, fields)
      case d@DefinitionT(qn) => ???
    }
  }

  def updateData(qn: QualifiedName, cons: Seq[PreConstructor]) : Unit = {
    for {
      data <- getData(qn)
      _ = data.cons == null match {
        case true => Right(())
        case false => typingError(s"Data $qn already has constructors.")
      }
      cons <- cons.reduceCons(using Context.empty + data.paramTys)
    } yield mContent(qn) = DataT(qn)(data.paramTys, data.level, cons)
  }

  def updateRecord(qn: QualifiedName, fields: Seq[PreField]) : Unit = {
    for {
      record <- getRecord(qn)
      _ = record.fields == null match {
        case true => Right(())
        case false => typingError(s"Record $qn already has fields.")
      }
      fields <- fields.reduceFields(using Context.empty + record.paramTys + ("self" ∷ Whnf.WRecord(qn, record.paramTys.vars.toList)))
    } yield mContent(qn) = RecordT(qn)(record.paramTys, record.level, fields)
  }

  private def (cons: Seq[PreConstructor]) reduceCons(using Γ: Context)(using Σ: Signature) : Result[Seq[Constructor]] = 
    cons.liftMap(con => con.argTys.tele.map(ConstructorT(con.name, _)))
  private def (fields: Seq[PreField]) reduceFields(using Γ: Context)(using Σ: Signature) : Result[Seq[Field]] = 
    fields.liftMap(f => f.ty.whnf.map(FieldT(f.name, _)))
}
