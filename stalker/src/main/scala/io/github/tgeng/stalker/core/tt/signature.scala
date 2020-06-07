package io.github.tgeng.stalker.core.tt

import scala.collection.Map
import scala.collection.Seq
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.HashMap
import io.github.tgeng.common._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.common.QualifiedName
import reduction.toWhnfs
import reduction.toWhnf
import typing._
import stringBindingOps._
import userInputBarBarBar._
import lhsOps._

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum DeclarationT[+S <: Status, +T] {
  case DataT(val qn: QualifiedName)(val paramTys: List[Binding[T]], val ty: T, val cons: Seq[ConstructorT[T]] | Null)
  case RecordT(val qn: QualifiedName)(val paramTys: List[Binding[T]], val ty: T, val fields: Seq[FieldT[T]] | Null)
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
  case UImpossible
}

import UncheckedRhs._

type Declaration = DeclarationT[Checked, Type]
type Data = DataT[Checked, Type]
type Record = RecordT[Checked, Type]
type Definition = DefinitionT[Checked, Type]
type Constructor = ConstructorT[Type]
type Field = FieldT[Type]
type Clause = ClauseT[Checked, Type]

trait Signature {
  def getData(qn: QualifiedName) : Result[Data]
  def getRecord(qn: QualifiedName) : Result[Record]
  def getDefinition(qn: QualifiedName) : Result[Definition]
}

trait MapBasedSignature (
  val data: Map[QualifiedName, Data],
  val records: Map[QualifiedName, Record],
  val definitions: Map[QualifiedName, Definition]
  ) extends Signature {

  def getData(qn: QualifiedName) : Result[Data] = data get qn match {
    case Some(d) => Right(d)
    case _ => typingError(e"No data schema found for $qn")
  }

  def getRecord(qn: QualifiedName) : Result[Record] = records get qn match {
    case Some(r) => Right(r)
    case _ => typingError(e"No record schema found for $qn")
  }

  def getDefinition(qn: QualifiedName) : Result[Definition] = definitions get qn match {
    case Some(d) => Right(d)
    case _ => typingError(e"No definition found for $qn")
  }
}

extension dataTypingOps on (self: Data) {
  def apply(name: String) : Result[Constructor] = self.getCons.flatMap {
    _.find(_.name == name) match {
      case Some(c) => Right(c)
      case None => typingError(e"Cannot find constructor '$name' for data ${self.qn}.")
    }
  } 

  def getCons : Result[Seq[Constructor]] = {
    val cons = self.cons
    if (cons == null) return typingError(e"Record ${self.qn} is declared but not initialized.")
    Right(cons)
  }
}

extension recordTypingOps on (self: Record) {
  def apply(name: String) : Result[Field] = self.getFields.flatMap {
    _.find(_.name == name) match {
    case Some(f) => Right(f) 
    case None => typingError(e"Cannot find field '$name' for record ${self.qn}.") 
    } 
  }

  def getFields : Result[Seq[Field]] = {
    val fields = self.fields
    if (fields == null) return typingError(e"Record ${self.qn} is declared but not initialized.")
    Right(fields)
  }
}

type PreDefinition = DefinitionT[Unchecked, Term]
type PreDeclaration = DeclarationT[Unchecked, Term]
type PreData = DataT[Unchecked, Term]
type PreRecord = RecordT[Unchecked, Term]
type PreConstructor = ConstructorT[Term]
type PreField = FieldT[Term]
type PreClause = ClauseT[Unchecked, Term]

object SignatureBuilder {
  def create : SignatureBuilder = {
    val sb = SignatureBuilder(HashMap.empty, HashMap.empty, HashMap.empty)
    import builtins._
    import scala.language.postfixOps

    assertResult(sb += levelType)
    assertResult(sb += typeType)
    assertResult(sb += lsucFn)
    assertResult(sb += lmaxFn)
    assertResult(sb += idType)
    sb
  }
}

class SignatureBuilder(
  val mData: mutable.Map[QualifiedName, Data],
  val mRecords: mutable.Map[QualifiedName, Record],
  val mDefinitions: mutable.Map[QualifiedName, Definition],
) extends MapBasedSignature(mData, mRecords, mDefinitions) {
  given Signature = this
  given Context = Context.empty

  def += (d: PreDeclaration) : Result[Unit] = {
    import Term._
    import Whnf._
    import CoPattern._
    if (mDefinitions.contains(d.qn)) {
      return duplicatedDefinitionError(s"${d.qn} has been defined already.")
    }
    d match {
      case d@DataT(qn) => for {
        level <- d.paramTys.level
        _Δ <- d.paramTys.toWhnfs
        cons <- d.cons match {
          case null => Right(null)
          case cons : Seq[PreConstructor] => cons.reduceCons(using Context.empty + _Δ)
        }
        ty = WType(TWhnf(level))
        _ = mData(qn) = new Data(qn)(_Δ, ty, cons)
        _ <- this += DefinitionT(qn)(
          _Δ.foldRight(TWhnf(ty))((binding, bodyTy) => TWhnf(WFunction(binding.map(TWhnf(_)), bodyTy))),
          Seq(UncheckedClause(
            _Δ.pvars.map(QPattern(_)).toList,
            UTerm(TWhnf(WData(qn, _Δ.vars.toList)))
          )),
          null
        )
      } yield ()
      case r@RecordT(qn) => for {
        level <- r.paramTys.level
        _Δ <- r.paramTys.toWhnfs
        fields <- r.fields match {
          case null => Right(null)
          case fields: Seq[PreField] => fields.reduceFields(using Context.empty + _Δ + ("self" ∷ Whnf.WRecord(qn, _Δ.vars.toList)))
        }
        ty = WType(TWhnf(level))
        _ = mRecords(qn) = new Record(qn)(_Δ, ty, fields)
        _ <- this += DefinitionT(qn)(
          _Δ.foldRight(TWhnf(ty))((binding, bodyTy) => TWhnf(WFunction(binding.map(TWhnf(_)), bodyTy))),
          Seq( UncheckedClause(
            _Δ.pvars.map(QPattern(_)).toList,
            UTerm(TWhnf(WData(qn, _Δ.vars.toList)))
          )),
          null
        )
      } yield ()
      case d@DefinitionT(qn) => {
        val clauses = ArrayBuffer[Clause]()
        for {
          _ <- d.ty.level
          ty <- d.ty.toWhnf
          _ = mDefinitions(qn) = new Definition(qn)(ty, clauses, null)
          _Q <- (d.clauses
            .map {
              case UncheckedClause(lhs, rhs) => (Set.empty[(Term /? Pattern) ∷ Type], lhs) |-> rhs
            }
            .toList ||| (qn, Nil) ∷ ty).elaborate(using clauses)
          _ = mDefinitions(qn) = new Definition(qn)(ty, clauses, _Q)
        } yield ()
      }
    }
  }

  def updateData(qn: QualifiedName, cons: Seq[PreConstructor]) : Result[Unit] = {
    for {
      data <- getData(qn)
      _ = data.cons == null match {
        case true => Right(())
        case false => typingError(e"Data $qn already has constructors.")
      }
      cons <- cons.reduceCons(using Context.empty + data.paramTys)
    } yield mData(qn) = new DataT(qn)(data.paramTys, data.ty, cons)
  }

  def updateRecord(qn: QualifiedName, fields: Seq[PreField]) : Result[Unit] = {
    for {
      record <- getRecord(qn)
      _ = record.fields == null match {
        case true => Right(())
        case false => typingError(e"Record $qn already has fields.")
      }
      fields <- fields.reduceFields(using Context.empty + record.paramTys + ("self" ∷ Whnf.WRecord(qn, record.paramTys.vars.toList)))
    } yield mRecords(qn) = new RecordT(qn)(record.paramTys, record.ty, fields)
  }

  private def (cons: Seq[PreConstructor]) reduceCons(using Γ: Context)(using Σ: Signature) : Result[Seq[Constructor]] = 
    cons.liftMap{
      con => for _ <- con.argTys.level
                 wArgTys <- con.argTys.toWhnfs
             yield ConstructorT(con.name, wArgTys)
    }
  private def (fields: Seq[PreField]) reduceFields(using Γ: Context)(using Σ: Signature) : Result[Seq[Field]] = 
    fields.liftMap{
      f => for _ <- f.ty.level
              wTy <- f.ty.toWhnf
           yield FieldT(f.name, wTy)
    }
}
