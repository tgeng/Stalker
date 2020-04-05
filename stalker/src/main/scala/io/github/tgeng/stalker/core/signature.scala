package io.github.tgeng.stalker.core

import scala.collection.Map
import scala.collection.Seq
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import io.github.tgeng.stalker.common.QualifiedName
import typing._
import typing.checkElim
import typing.checkTerm

enum Status {
  case Unchecked()
  case Checked()
}

import Status._

enum DeclarationT[S <: Status, +C[_]] {
  case DataT(qn: QualifiedName, paramTys: Telescope, level: Int, cons: C[Constructor])
  case RecordT(qn: QualifiedName, paramTys: Telescope, level: Int, fields: C[Field])
  case DefinitionT(qn: QualifiedName, ty: Type, clauses: C[Clause[S]])
}

import DeclarationT._

case class Constructor(name: String, argTys: Telescope)

case class Field(name: String, ty: Type)

enum Clause[T <: Status] {
  case UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs) extends Clause[Unchecked]
  case CheckedClause(bindings: Telescope, lhs: List[CoPattern], rhs: Term, ty: Type) extends Clause[Checked]
}

import Clause._

enum UncheckedRhs {
  case UTerm(t: Term)
  case Impossible
}

import UncheckedRhs._

type SignatureT[+C[_]] = Map[QualifiedName, DeclarationT[Checked, C]]

extension signatureTOps on [C[_]](Σ: SignatureT[C]) {
  def getData(qn: QualifiedName) : Result[DataT[Checked, C]] = Σ get qn match {
    case Some(d : DataT[Checked, C]) => Right(d.asInstanceOf[DataT[Checked, C]])
    case _ => typingError(s"No data schema found for $qn")
  }

  def getRecord(qn: QualifiedName) : Result[RecordT[Checked, C]] = Σ get qn match {
    case Some(r : RecordT[Checked, C]) => Right(r.asInstanceOf[RecordT[Checked, C]])
    case _ => typingError(s"No record schema found for $qn")
  }

  def getDefinition(qn: QualifiedName) : Result[DefinitionT[Checked, C]] = Σ get qn match {
    case Some(d : DefinitionT[Checked, C]) => Right(d.asInstanceOf[DefinitionT[Checked, C]])
    case _ => typingError(s"No definition found for $qn")
  }
}

type Declaration = DeclarationT[Checked, Seq]
type Data = DataT[Checked, Seq]
type Record = RecordT[Checked, Seq]
type Definition = DefinitionT[Checked, Seq]
type Signature = Map[QualifiedName, Declaration]

object mutable {
  type Declaration = DeclarationT[Checked, ArrayBuffer]
  type Data = DataT[Checked, ArrayBuffer]
  type Record = RecordT[Checked, ArrayBuffer]
  type Definition = DefinitionT[Checked, ArrayBuffer]
  type Signature = HashMap[QualifiedName, Declaration]

  import Term._
  import Whnf._
  given t as Telescope = Nil 

  object Signature {
    def create : Signature = HashMap[QualifiedName, Declaration]()
  }

  extension signatureOps on (Σ: Signature) {
    def += (d: Data) : Result[Unit] = {
      given s as Signature = Σ
      for {
        _ <- d.paramTys.level
      } yield Σ(d.qn) = d
    } 

    def += (qn: QualifiedName, c: Constructor) : Result[Unit] = {
      given s as Signature = Σ
      for {
        data <- Σ getData qn
        cL <- c.argTys.level(using data.paramTys)
        _ <- cL <= data.level match {
          case true => Right(())
          case _ => typingError(s"Level of arguments in constructor $c is above that of data declaration $qn.")
        }
      } yield { data.cons.append(c); () }
    }

    def += (r: Record) : Result[Unit] = {
      given s as Signature = Σ
      for {
        _ <- r.paramTys.level
      } yield Σ(r.qn) = r
    } 

    def += (qn: QualifiedName, f: Field) : Result[Unit] = {
      given s as Signature = Σ
      for {
        record <- Σ getRecord qn
        cL <- f.ty.level(using 
          record.paramTys :+ 
          WRecord(qn, ((record.paramTys.size - 1) to 0).map(i => TWhnf(WVar(i, Nil))).toList))
        _ <- cL <= record.level match {
          case true => Right(())
          case _ => typingError(s"Level of field $f is above that of record declaration $qn.")
        }
      } yield { record.fields.append(f); () }
    }

    def += (d: Definition) : Result[Unit] = {
      given s as Signature = Σ
      for {
        _ <- d.ty.level
      } yield Σ(d.qn) = d
    } 

    def += (qn: QualifiedName, c: Clause[Checked]) : Result[Unit] = {
      given s as Signature = Σ
      c match {
      case CheckedClause(_Δ, q̅, v, _B) => for {
          definition <- Σ getDefinition qn
          _ <- _Δ.level
          _ <- (TRedux(qn, Nil) ∷ definition.ty |- q̅.map(_.toElimination) ∷ _B).check(using _Δ)
          _ <- (v ∷ _B).check(using _Δ)
        } yield { definition.clauses.append(c); ()}
      }
    }
  }
}