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

enum Declaration {
  case DataDecl(qn: QualifiedName, paramTys: FTelescope, ty: FTerm)
  case DataDef(qn: QualifiedName, cons: Seq[Constructor])
  case RecordDecl(qn: QualifiedName, paramTys: FTelescope, ty: FTerm)
  case RecordDef(qn: QualifiedName, fields: Seq[Field])
  case Definition(qn: QualifiedName, ty: FTerm, clauses: Seq[UncheckedClause])

  def qn: QualifiedName
}

case class Constructor(name: String, argTys: FTelescope)

case class Field(name: String, ty: FTerm)

case class UncheckedClause(lhs: List[FCoPattern], rhs: UncheckedRhs)

enum UncheckedRhs {
  case UTerm(t: FTerm)
  case UImpossible
}

import Declaration._
import UncheckedRhs._

class Signature {
  private val sb = SignatureBuilder.create

  // def += (d: Declaration) : Result[Unit] = d match {
  //   case DataDecl(qn, paramTys, ty) => sb += DataT(qn)(paramTys.tt, ty.tt, null)
  //   case DataDef(qn, cons) => sb.updateData(qn, cons.map {
  //     case Constructor(name, argTys) => ConstructorT(name, argTys.tt)
  //   })
  //   case RecordDecl(qn, paramTys, ty) => sb += RecordT(qn)(paramTys.tt, ty.tt, null)
  //   case RecordDef(qn, fields) => NameContext.empty.withName("self") {
  //     sb.updateRecord(qn, fields.map{
  //       case Field(name, ty) => FieldT(name, ty.tt)
  //     })
  //   }
  //   case Definition(qn, ty, clauses) => 
  //     sb += DefinitionT(qn)(
  //       ty.tt, 
  //       clauses.map {
  //         case UncheckedClause(lhs, rhs) => NameContext.empty.withNames(lhs.flatMap(_.freeVars).distinct) {
  //           ClauseT.UncheckedClause(lhs.map(_.tt), rhs match {
  //             case UTerm(t) => TtUncheckedRhs.UTerm(t.tt)
  //             case UImpossible => TtUncheckedRhs.UImpossible
  //           })
  //         }
  //       }, 
  //       null)
  // }
}