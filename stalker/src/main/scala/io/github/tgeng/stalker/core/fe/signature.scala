package io.github.tgeng.stalker.core.fe

import scala.collection.Seq
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.error._
import io.github.tgeng.stalker.core.tt.Status
import io.github.tgeng.stalker.core.tt.SignatureBuilder
import io.github.tgeng.stalker.core.tt.{Signature => TtSignature}
import io.github.tgeng.stalker.core.tt.DeclarationT._
import io.github.tgeng.stalker.core.tt.ConstructorT
import io.github.tgeng.stalker.core.tt.ClauseT
import io.github.tgeng.stalker.core.tt.FieldT
import io.github.tgeng.stalker.core.tt.{UncheckedRhs => TtUncheckedRhs}
import telescopeOps._

enum Declaration {
  case DataDecl(qn: QualifiedName, paramTys: Telescope, level: Int)
  case DataDef(qn: QualifiedName, cons: Seq[Constructor])
  case RecordDecl(qn: QualifiedName, paramTys: Telescope, level: Int)
  case RecordDef(qn: QualifiedName, fields: Seq[Field])
  case Definition(qn: QualifiedName, ty: Term, clauses: Seq[UncheckedClause])

  def qn: QualifiedName
}

case class Constructor(name: String, argTys: Telescope)

case class Field(name: String, ty: Term)

case class UncheckedClause(lhs: List[CoPattern], rhs: UncheckedRhs)

enum UncheckedRhs {
  case UTerm(t: Term)
  case UImpossible
}

import Declaration._
import UncheckedRhs._

class Signature {
  private val sb = SignatureBuilder()
  given NameContext = NameContext.empty

  def += (d: Declaration) : Result[Unit] = d match {
    case DataDecl(qn, paramTys, level) => for {
      paramTys <- paramTys.tt
      r <- sb += DataT(qn)(paramTys, level, null)
    } yield r
    case DataDef(qn, cons) => for {
      cons <- cons.liftMap {
        case Constructor(name, argTys) => for {
          argTys <- argTys.tt
        } yield ConstructorT(name, argTys)
      }
      r <- sb.updateData(qn, cons)
    } yield r
    case RecordDecl(qn, paramTys, level) => for {
      paramTys <- paramTys.tt
      r <- sb += RecordT(qn)(paramTys, level, null)
    } yield r
    case RecordDef(qn, fields) => for {
      fields <- fields.liftMap {
        case Field(name, ty) => for {
          ty <- ty.tt
        } yield FieldT(name, ty)
      }
      r <- sb.updateRecord(qn, fields)
    } yield r
    case Definition(qn, ty, clauses) => for {
      ty <- ty.tt
      clauses <- clauses.liftMap {
        case UncheckedClause(lhs, rhs) => for {
          lhs <- lhs.liftMap(_.tt)
          rhs <- rhs match {
            case UTerm(t) => t.tt.map(TtUncheckedRhs.UTerm(_))
            case UImpossible => Right(TtUncheckedRhs.UImpossible)
          }
        } yield ClauseT.UncheckedClause(lhs, rhs)
      }
      r <- sb += DefinitionT(qn)(ty, clauses, null)
    } yield r
  }
}