package io.github.tgeng.stalker.core.fe

import scala.collection.Seq
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.tt._

enum FDeclaration {
  case FDataDecl(qn: QualifiedName, paramTys: FTelescope, ty: FTerm)
  case FDataDef(qn: QualifiedName, cons: Seq[FConstructor])
  case FRecordDecl(qn: QualifiedName, paramTys: FTelescope, ty: FTerm)
  case FRecordDef(qn: QualifiedName, fields: Seq[FField])
  case FDefinition(qn: QualifiedName, ty: FTerm, clauses: Seq[FUncheckedClause])

  def qn: QualifiedName
}

case class FConstructor(name: String, argTys: FTelescope)

case class FField(name: String, ty: FTerm)

case class FUncheckedClause(lhs: List[FCoPattern], rhs: FUncheckedRhs)

enum FUncheckedRhs {
  case FUTerm(t: FTerm)
  case FUImpossible
}

import FDeclaration._
import FUncheckedRhs._
import UncheckedRhs._

class FSignature {
  import ftConversion.{given _, _}
  private val sb = SignatureBuilder.create

  def += (d: FDeclaration)(using ns: Namespace) : Result[Unit] = {
    given LocalIndices = LocalIndices()
    d match {
      case FDataDecl(qn, paramTys, ty) =>
        for paramTys <- paramTys.liftMap(_.toTt)
            ty <- ty.toTt
            _ <- sb += PreData(qn)(paramTys, ty, null)
        yield ()
      case FDataDef(qn, cons) =>
        for cons <- cons.liftMap(_.toTt)
            _ <- sb.updateData(qn, cons)
        yield ()
      case FRecordDecl(qn, paramTys, ty) =>
        for paramTys <- paramTys.liftMap(_.toTt)
            ty <- ty.toTt
            _ <- sb += PreRecord(qn)(paramTys, ty, null)
        yield ()
      case FRecordDef(qn, fields) =>
        for fields <- fields.liftMap(_.toTt)
            _ <- sb.updateRecord(qn, fields)
        yield ()
      case FDefinition(qn, ty, clauses) =>
        for ty <- ty.toTt
            clauses <- clauses.liftMap(_.toTt)
            _ <- sb += PreDefinition(qn)(ty, clauses, null)
        yield ()
    }
  }

  private given FT[FConstructor, PreConstructor] {
    def (c: FConstructor) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[PreConstructor] = c match {
      case FConstructor(name, argTys) =>
        for argTys <- argTys.toTt
        yield PreConstructor(name, argTys)
    }
  }

  private given FT[FField, PreField] {
    def (c: FField) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[PreField] = c match {
      case FField(name, ty) =>
        for ty <- ty.toTt
        yield PreField(name, ty)
    }
  }

  private given FT[FUncheckedRhs, UncheckedRhs] {
    def (c: FUncheckedRhs) toTt (using ctx: LocalIndices)(using ns: Namespace) : Result[UncheckedRhs] = c match {
      case FUTerm(t) => for t <- t.toTt yield UTerm(t)
      case FUImpossible => Right(UImpossible)
    }
  }

  def (c: FUncheckedClause) toTt (using ns: Namespace) : Result[PreClause] = c match {
    case FUncheckedClause(lhs, rhs) => {
      given LocalIndices = LocalIndices()
      for lhs <- lhs.liftMap(_.toTt)
          rhs <- rhs.toTt
      yield ClauseT.UncheckedClause(lhs, rhs)
    }
  }
}