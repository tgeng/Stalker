package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import scala.collection.Seq
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.MutableNamespace
import io.github.tgeng.stalker.core.tt._

import MutableNamespace.{_, given _}

enum FDeclaration {
  case FDataDecl(name: String, paramTys: FTelescope, level: FTerm)
  case FDataDef(name: String, cons: Seq[FConstructor])
  case FRecordDecl(name: String, paramTys: FTelescope, level: FTerm)
  case FRecordDef(name: String, fields: Seq[FField])
  case FDefinition(name: String, ty: FTerm, clauses: Seq[FUncheckedClause])
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

object FSignatureBuilder {
  def create = FSignatureBuilder()
}

class FSignatureBuilder extends Signature {
  import ftConversion.{given _, _}
  private val sb = SignatureBuilder.create

  export sb.getData
  export sb.getRecord
  export sb.getDefinition

  def += (d: FDeclaration)(using ns: MutableNamespace) : Result[Unit] = {
    given LocalIndices = LocalIndices()
    d match {
      case FDataDecl(name, paramTys, level) =>
        for paramTys <- paramTys.liftMap(_.toTt)
            level <- level.toTt
            _ <- sb += PreData(ns.qn / name)(paramTys, level, null)
        yield ns.addDeclaration(name)
      case FDataDef(name, cons) =>
        for cons <- cons.liftMap(_.toTt)
            _ <- sb.updateData(ns.qn / name, cons)
        yield ns.addDeclaration(name, cons.map(_.name))
      case FRecordDecl(name, paramTys, level) =>
        for paramTys <- paramTys.liftMap(_.toTt)
            level <- level.toTt
            _ <- sb += PreRecord(ns.qn / name)(paramTys, level, null)
        yield ns.addDeclaration(name)
      case FRecordDef(name, fields) =>
        for fields <- fields.liftMap(_.toTt)
            _ <- sb.updateRecord(ns.qn / name, fields)
        yield ()
      case FDefinition(name, ty, clauses) =>
        for ty <- ty.toTt
            clauses <- clauses.liftMap(_.toTt)
            d = PreDefinition(ns.qn / name)(ty, clauses, null)
            _ <- sb += d
        yield ns.importNs(d)
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
      val ctx = LocalIndices()
      ctx.addAllFromCoPatterns(lhs)
      given LocalIndices = ctx
      for lhs <- lhs.liftMap(_.toTt)
          rhs <- rhs.toTt
      yield ClauseT.UncheckedClause(lhs, rhs)
    }
  }
}