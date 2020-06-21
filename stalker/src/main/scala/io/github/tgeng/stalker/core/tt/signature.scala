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
  case DefinitionT(val qn: QualifiedName)(val ty: T, val clauses: Seq[ClauseT[S, T]] | Null, val ct: CaseTree | Null)

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
  
  given Signature = this
  given Context = Context.empty

  import Term._
  import Whnf._
  import CoPattern._

  def elaborate(d: PreDeclaration): Result[Seq[Declaration]] = d match {
    case d: PreData => for (data, defs) <- elaborateData(d)
                       yield data +: defs
    case r: PreRecord => for (record, defs) <- elaborateRecord(r)
                         yield record +: defs
    case d: PreDefinition => elaborateDefinition(d).map(Seq(_))
  }

  def elaborateData(d: PreData): Result[(Data, Seq[Definition])] = d match {
    case DataT(qn) => for {
      _ <- d.paramTys.levelBound
      _Δ <- d.paramTys.toWhnfs
      res <- withCtxExtendedBy(_Δ) {
        for _ <- d.ty.level
            ty <- d.ty.toWhnf
            levelBound <- ty match {
              case WType(l) =>
                for l <- l.toWhnf
                yield l
              case _ => typingErrorWithCtx(e"Cannot reduce ${d.ty} to a Type at some level.")
            }
            elaborated = new Data(qn)(_Δ, WType(TWhnf(levelBound)), null)
            extendSignature = ExtendedSignature(this, elaborated)
            typeCon <- extendSignature.dataTypeCon(elaborated)
            (data, valueCons) <- d.cons match {
              case null => Right(elaborated, Nil)
              case preCons : Seq[PreConstructor] => ExtendedSignature(extendSignature, typeCon).augmentData(d.qn, preCons)
            }
        yield (data, typeCon +: valueCons)
      }
    } yield res
  }

  protected def dataTypeCon(d: Data): Result[Definition] = elaborateDefinition(
    PreDefinition(d.qn)(
      d.paramTys.foldRight(TWhnf(d.ty))((binding, bodyTy) => TWhnf(WFunction(binding.map(TWhnf(_)), bodyTy))),
      Seq(UncheckedClause(
        d.paramTys.pvars.map(QPattern(_)).toList,
        UTerm(TWhnf(WData(d.qn, d.paramTys.vars.toList)))
      )),
      null
    ))

  def elaborateRecord(r: PreRecord): Result[(Record, Seq[Definition])] = r match {
    case RecordT(qn) => for {
      _ <- r.paramTys.levelBound
      _Δ <- r.paramTys.toWhnfs
      res <- withCtxExtendedBy(_Δ) {
        for _ <- r.ty.level
            ty <- r.ty.toWhnf
            levelBound <- ty match {
              case WType(l) =>
                for l <- l.toWhnf
                yield l
              case _ => typingErrorWithCtx(e"Cannot reduce ${r.ty} to a Type at some level.")
            }
            elaborated = new Record(qn)(_Δ, WType(TWhnf(levelBound)), null)
            extendSignature = ExtendedSignature(this, elaborated)
            typeCon <- extendSignature.recordTypeCon(elaborated)
            record <- r.fields match {
              case null => Right(elaborated)
              case preFields: Seq[PreField] => ExtendedSignature(extendSignature, typeCon).augmentRecord(r.qn, preFields)
            }
        yield (record, Seq(typeCon))
      }
    } yield res
  }

  protected def recordTypeCon(r: Record): Result[Definition] = elaborateDefinition(
    PreDefinition(r.qn)(
      r.paramTys.foldRight(TWhnf(r.ty))((binding, bodyTy) => TWhnf(WFunction(binding.map(TWhnf(_)), bodyTy))),
      Seq(UncheckedClause(
        r.paramTys.pvars.map(QPattern(_)).toList,
        UTerm(TWhnf(WRecord(r.qn, r.paramTys.vars.toList)))
      )),
      null
    ))

  def elaborateDefinition(d: PreDefinition): Result[Definition] = d match {
    case d@DefinitionT(qn) => {
      for {
        _ <- d.ty.level
        ty <- d.ty.toWhnf
        elaborated = new Definition(qn)(ty, null, null)
        r <- d.clauses match {
          case null => Right(elaborated)
          case preClauses: Seq[PreClause] => ExtendedSignature(this, elaborated).augmentDef(d.qn, preClauses)
        }
      } yield r
    }
  }

  def augmentData(qn: QualifiedName, preCons: Seq[PreConstructor]): Result[(Data, Seq[Definition])] = {
    for {
      data <- getData(qn)
      _ = data.cons == null match {
        case true => Right(())
        case false => typingErrorWithCtx(e"Data $qn already has constructors.")
      }
      processed = ArrayBuffer[Constructor]()
      augmented = new Data(qn)(data.paramTys, data.ty, processed)
      WType(levelBound) = data.ty
      _ <- ExtendedSignature(this, augmented).processCons(qn, levelBound, preCons.toList, processed)(using Context.empty + data.paramTys)
    } yield (augmented, Nil) // Add constructor defs when implicit parameters are supported
  }

  protected def processCons(qn: QualifiedName, levelBound: Term, preCons: List[PreConstructor], processed: ArrayBuffer[Constructor])(using Context): Result[Unit] = preCons match {
    case Nil => Right(())
    case con :: rest => 
      for l <- con.argTys.levelBound
          con <- l match {
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
          _ = processed.addOne(con)
          r <- processCons(qn, levelBound, rest, processed)
      yield r
  }

  def augmentRecord(qn: QualifiedName, preFields: Seq[PreField]) : Result[Record] = {
    for {
      record <- getRecord(qn)
      _ = record.fields == null match {
        case true => Right(())
        case false => typingErrorWithCtx(e"Record $qn already has fields.")
      }
      processed = ArrayBuffer[Field]()
      augmented = new Record(qn)(record.paramTys, record.ty, processed)
      WType(levelBound) = record.ty
      _ <- ExtendedSignature(this, augmented).processFields(qn, levelBound, preFields.toList, processed)(using Context.empty + record.paramTys)
    } yield augmented
  }

  protected def processFields(qn: QualifiedName, levelBound: Term, preFields: List[PreField], processed: ArrayBuffer[Field])(using Context): Result[Unit] = preFields match {
    case Nil => Right(())
    case preField :: rest => for {
      l <- preField.ty.level
      _ <- (TWhnf(l) <= levelBound) match {
       case Right(true) => Right(())
       case Right(false) => typingErrorWithCtx(e"Field ${preField.name} at level $l is not within the specified level bound $levelBound of record schema $qn.")
       case _ => typingErrorWithCtx(e"Cannot determine if field ${preField.name} at level $l is within the specified level bound $levelBound of record schema $qn.")
      }
      fieldTy <- preField.ty.toWhnf
      field = Field(preField.name, fieldTy)
      _ = processed.addOne(field)
      r <- processFields(qn, levelBound, rest, processed)
      } yield r
  }

  def augmentDef(qn: QualifiedName, preClauses: Seq[PreClause]) = {
    val clauses = ArrayBuffer[Clause]()
    for {
      d <- getDefinition(qn)
      _ = d.clauses == null match {
        case true => Right(())
        case false => typingErrorWithCtx(e"Definition $qn is already fully defined.")
      }
      augmented = new Definition(qn)(d.ty, clauses, null)
      _Q <- (
        preClauses.map {
          case UncheckedClause(lhs, rhs) => (Set.empty[(Term /? Pattern) ∷ Type], lhs) |-> rhs
        }
        .toList ||| (qn, Nil) ∷ d.ty
        ).elaborate(using clauses)(using Context.empty)(using ExtendedSignature(this, augmented))
    } yield new Definition(qn)(d.ty, clauses, _Q)
  }
}

object EmptySignature extends Signature {
  def getData(qn: QualifiedName) : Result[Data] = typingError(e"No data schema found for $qn")
  def getRecord(qn: QualifiedName) : Result[Record] = typingError(e"No record schema found for $qn")
  def getDefinition(qn: QualifiedName) : Result[Definition] = typingError(e"No definition found for $qn")
}

trait MapBasedSignature (
  val data: Map[QualifiedName, Data],
  val records: Map[QualifiedName, Record],
  val definitions: Map[QualifiedName, Definition],
  val fallback: Signature
  ) extends Signature {

  override def getData(qn: QualifiedName) : Result[Data] = data get qn match {
    case Some(d) => Right(d)
    case _ => fallback.getData(qn)
  }

  override def getRecord(qn: QualifiedName) : Result[Record] = records get qn match {
    case Some(r) => Right(r)
    case _ => fallback.getRecord(qn)
  }

  override def getDefinition(qn: QualifiedName) : Result[Definition] = definitions get qn match {
    case Some(d) => Right(d)
    case _ => fallback.getDefinition(qn)
  }
}

class ExtendedSignature(val fallback: Signature, val ext: Declaration*) extends Signature {
  private val dataDecls : Seq[Data] = ext.collect { case d: Data => d}
  private val recordDecls : Seq[Record] = ext.collect { case r: Record => r}
  private val defDecls : Seq[Definition] = ext.collect { case d: Definition => d}
  def getData(qn: QualifiedName) : Result[Data] = dataDecls.find(_.qn == qn) match {
    case Some(d) => Right(d)
    case _ => fallback.getData(qn)
  }
  def getRecord(qn: QualifiedName) : Result[Record] = recordDecls.find(_.qn == qn) match {
    case Some(r) => Right(r)
    case _ => fallback.getRecord(qn)
  }
  def getDefinition(qn: QualifiedName) : Result[Definition] = defDecls.find(_.qn == qn) match {
    case Some(d) => Right(d)
    case _ => fallback.getDefinition(qn)
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
  def create(fallback: Signature) : SignatureBuilder = SignatureBuilder(HashMap.empty, HashMap.empty, HashMap.empty, fallback)
}

class SignatureBuilder(
  val mData: mutable.Map[QualifiedName, Data],
  val mRecords: mutable.Map[QualifiedName, Record],
  val mDefinitions: mutable.Map[QualifiedName, Definition],
  fallback: Signature
) extends MapBasedSignature(mData, mRecords, mDefinitions, fallback) {

  def declarations = data.values.asInstanceOf[Seq[Declaration]] ++ records.values ++ definitions.values

  def += (d: Declaration): Unit = d match {
    case d : Data => getData(d.qn) match {
      case Right(existingD) if (existingD.paramTys != d.paramTys || existingD.ty != d.ty || existingD.cons != null) =>
        throw IllegalArgumentException(s"Data schema ${d.qn} is already defined.")
      case _ => mData(d.qn) = d
    }
    case r : Record => getRecord(r.qn) match {
      case Right(existingR) if (existingR.paramTys != r.paramTys || existingR.ty != r.ty || existingR.fields != null) =>
        throw IllegalArgumentException(s"Record schema ${d.qn} is already defined.")
      case _ => mRecords(r.qn) = r
    }
    case d : Definition => getDefinition(d.qn) match {
      case Right(existingD) if (existingD.ty != d.ty || existingD.clauses != d.clauses || existingD.ct != null) =>
        throw IllegalArgumentException(s"Definition schema ${d.qn} is already defined.")
      case _ => mDefinitions(d.qn) = d
    }
  }

  def ++= (decls: Iterable[Declaration]): Unit = decls.foreach(this += _)
}
