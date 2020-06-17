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
import reduction.<=
import typing._
import stringBindingOps._
import userInputBarBarBar._
import lhsOps._
import utils._

import io.github.tgeng.common.debug._

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
  def declarations : Seq[Declaration]
}

object EmptySignature extends Signature {
  def getData(qn: QualifiedName) : Result[Data] = typingError(e"No data schema found for $qn")
  def getRecord(qn: QualifiedName) : Result[Record] = typingError(e"No record schema found for $qn")
  def getDefinition(qn: QualifiedName) : Result[Definition] = typingError(e"No definition found for $qn")
  def declarations = Seq.empty
}

trait MapBasedSignature (
  val data: Map[QualifiedName, Data],
  val records: Map[QualifiedName, Record],
  val definitions: Map[QualifiedName, Definition],
  val fallback: Signature
  ) extends Signature {

  def getData(qn: QualifiedName) : Result[Data] = data get qn match {
    case Some(d) => Right(d)
    case _ => fallback.getData(qn)
  }

  def getRecord(qn: QualifiedName) : Result[Record] = records get qn match {
    case Some(r) => Right(r)
    case _ => fallback.getRecord(qn)
  }

  def getDefinition(qn: QualifiedName) : Result[Definition] = definitions get qn match {
    case Some(d) => Right(d)
    case _ => fallback.getDefinition(qn)
  }

  def declarations = data.values.asInstanceOf[Seq[Declaration]] ++ records.values ++ definitions.values
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
  def create(fallback: Signature) : SignatureBuilder = SignatureBuilder(HashMap.empty, HashMap.empty, HashMap.empty, fallback)
}

class SignatureBuilder(
  val mData: mutable.Map[QualifiedName, Data],
  val mRecords: mutable.Map[QualifiedName, Record],
  val mDefinitions: mutable.Map[QualifiedName, Definition],
  fallback: Signature
) extends MapBasedSignature(mData, mRecords, mDefinitions, fallback) {
  given Signature = this
  given Context = Context.empty

  def importDecl (d: Declaration) : Result[Unit] = d match {
    case d : Data => getData(d.qn) match {
      case Right(existingD) => {
        if (existingD.paramTys != d.paramTys || existingD.ty != d.ty || existingD.cons != d.cons) {
          duplicatedDefinitionError(e"Data schema ${d.qn} is already defined.")
        } else {
          Right(())
        }
      }
      case _ => Right(mData(d.qn) = d)
    }
    case r : Record => getRecord(r.qn) match {
      case Right(existingR) => {
        if (existingR.paramTys != r.paramTys || existingR.ty != r.ty || existingR.fields != r.fields) {
          duplicatedDefinitionError(e"Record schema ${r.qn} is already defined.")
        } else {
          Right(())
        }
      }
      case _ => Right(mRecords(r.qn) = r)
    }
    case d : Definition => getDefinition(d.qn) match {
      case Right(existingD) => {
        if (existingD.ty != d.ty || existingD.clauses != d.clauses || existingD.ct != d.ct) {
          duplicatedDefinitionError(e"Definition ${d.qn} is already defined.")
        } else {
          Right(())
        }
      }
      case _ => Right(mDefinitions(d.qn) = d)
    }
  }

  def += (d: PreDeclaration) : Result[Unit] = {
    import Term._
    import Whnf._
    import CoPattern._
    if (mDefinitions.contains(d.qn)) {
      return duplicatedDefinitionError(e"${d.qn} has been defined already.")
    }
    d match {
      case d@DataT(qn) => for {
        _ <- d.paramTys.levelBound
        _Δ <- d.paramTys.toWhnfs
        _ <- withCtxExtendedBy(_Δ) {
          for _ <- d.ty.level
              ty <- d.ty.toWhnf
              levelBound <- ty match {
                case WType(l) =>
                  for l <- l.toWhnf
                  yield l
                case _ => typingErrorWithCtx(e"Cannot reduce ${d.ty} to a Type at some level.")
              }
              _ = mData(qn) = new Data(qn)(_Δ, WType(TWhnf(levelBound)), null)
              _ <- this += PreDefinition(qn)(
                _Δ.foldRight(TWhnf(ty))((binding, bodyTy) => TWhnf(WFunction(binding.map(TWhnf(_)), bodyTy))),
                Seq(UncheckedClause(
                  _Δ.pvars.map(QPattern(_)).toList,
                  UTerm(TWhnf(WData(qn, _Δ.vars.toList)))
                )),
                null
              )
              cons <- d.cons match {
                case null => Right(null)
                case cons : Seq[PreConstructor] => cons.reduceCons(d.qn, ty)
              }
              _ = mData(qn) = new Data(qn)(_Δ, ty, cons)
          yield ()
        }
      } yield ()
      case r@RecordT(qn) => for {
        _ <- r.paramTys.levelBound
        _Δ <- r.paramTys.toWhnfs
        _ <- withCtxExtendedBy(_Δ) {
          for _ <- r.ty.level
              ty <- r.ty.toWhnf
              levelBound <- ty match {
                case WType(l) =>
                  for l <- l.toWhnf
                  yield l
                case _ => typingErrorWithCtx(e"Cannot reduce ${r.ty} to a Type at some level.")
              }
              _ = mRecords(qn) = new Record(qn)(_Δ, WType(TWhnf(levelBound)), null)
              _ <- this += PreDefinition(qn)(
                _Δ.foldRight(TWhnf(ty))((binding, bodyTy) => TWhnf(WFunction(binding.map(TWhnf(_)), bodyTy))),
                Seq( UncheckedClause(
                  _Δ.pvars.map(QPattern(_)).toList,
                  UTerm(TWhnf(WData(qn, _Δ.vars.toList)))
                )),
                null
              )
              fields <- r.fields match {
                case null => Right(null)
                case fields: Seq[PreField] => fields.reduceFields(r.qn, ty)(using Context.empty + _Δ + ("self" ∷ Whnf.WRecord(qn, _Δ.vars.toList)))
              }
              _ = mRecords(qn) = new Record(qn)(_Δ, ty, fields)
          yield ()
        }
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
        case false => typingErrorWithCtx(e"Data $qn already has constructors.")
      }
      cons <- cons.reduceCons(data.qn, data.ty)(using Context.empty + data.paramTys)
    } yield mData(qn) = new DataT(qn)(data.paramTys, data.ty, cons)
  }

  def updateRecord(qn: QualifiedName, fields: Seq[PreField]) : Result[Unit] = {
    for {
      record <- getRecord(qn)
      _ = record.fields == null match {
        case true => Right(())
        case false => typingErrorWithCtx(e"Record $qn already has fields.")
      }
      fields <- fields.reduceFields(record.qn, record.ty)(using Context.empty + record.paramTys + ("self" ∷ Whnf.WRecord(qn, record.paramTys.vars.toList)))
    } yield mRecords(qn) = new RecordT(qn)(record.paramTys, record.ty, fields)
  }

  import Term._
  import Whnf._

  private def (cons: Seq[PreConstructor]) reduceCons(qn: QualifiedName, dataTy: Whnf)(using Γ: Context)(using Σ: Signature) : Result[Seq[Constructor]] = 
    dataTy match {
      case WType(levelBound) => {
        cons.liftMap{
          con => for l <- con.argTys.levelBound
                     r <- l match {
                       case Some(l) => for {
                         _ <- (TWhnf(l) <= levelBound) match {
                          case Right(true) => Right(())
                          case Right(false) => typingErrorWithCtx(e"Arguments to constructor ${con.name} at level $l is not within the specified level bound $levelBound of data schema $qn.")
                          case _ => typingErrorWithCtx(e"Cannot determine if arguments to constructor ${con.name} at level $l is within the specified level bound $levelBound of data schema $qn.")
                         }
                         wArgTys <- con.argTys.toWhnfs
                       } yield ConstructorT(con.name, wArgTys)
                       case None => typingErrorWithCtx(e"Arguments to constructor ${con.name} is potentially unbound and hence is not within the specified level bound $levelBound of data schema $qn.")
                     }
                 yield r
        }
      }
      case _ => throw AssertionError("This case should have been prevented when adding this data schema to the signature.")
    }
  private def (fields: Seq[PreField]) reduceFields(qn: QualifiedName, recordTy: Whnf)(using Γ: Context)(using Σ: Signature) : Result[Seq[Field]] = 
    recordTy match {
      case WType(levelBound) => {
        fields.liftMap{
          field => for l <- field.ty.level
                     _ <- (TWhnf(l) <= levelBound) match {
                      case Right(true) => Right(())
                      case Right(false) => typingErrorWithCtx(e"Field ${field.name} at level $l is not within the specified level bound $levelBound of record schema $qn.")
                      case _ => typingErrorWithCtx(e"Cannot determine if field ${field.name} at level $l is within the specified level bound $levelBound of record schema $qn.")
                     }
                     fieldTy <- field.ty.toWhnf
                 yield FieldT(field.name, fieldTy)
        }
      }
      case _ => throw AssertionError("This case should have been prevented when adding this data schema to the signature.")
    }
}
