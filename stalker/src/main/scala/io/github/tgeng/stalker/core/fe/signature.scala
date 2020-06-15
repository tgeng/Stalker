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
  case FData(name: String, paramTys: FTelescope, ty: FTerm, cons: Seq[FConstructor] | Null)
  case FDataDef(name: String, cons: Seq[FConstructor])

  case FRecord(name: String, paramTys: FTelescope, ty: FTerm, fields: Seq[FField] | Null)
  case FRecordDef(name: String, fields: Seq[FField])

  case FDefinition(name: String, ty: FTerm, clauses: Seq[FUncheckedClause])

  override def toString = this match {
    case FData(name, paramTys ,ty, cons) => s"""FData("$name", $paramTys, $ty, $cons)"""
    case FDataDef(name, cons) => s"""FDataDef("$name", $cons)"""

    case FRecord(name, paramTys ,ty, fields) => s"""FRecord("$name", $paramTys, $ty, $fields)"""
    case FRecordDef(name, fields) => s"""FRecordDef("$name", $fields)"""

    case FDefinition(name, ty, clauses) => s"""FDefinition("$name", $ty, $clauses)"""
  }
}

case class FConstructor(name: String, argTys: FTelescope) {
  override def toString = s"""FConstructor("$name", $argTys)"""
}

case class FField(name: String, ty: FTerm) {
  override def toString = s"""FField("$name", $ty)"""
}

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
  private val sb = SignatureBuilder.create(builtins.signature)

  export sb.getData
  export sb.getRecord
  export sb.getDefinition
  export sb.allDeclarations

  def += (d: FDeclaration)(using ns: MutableNamespace) : Result[Unit] = {
    given LocalIndices = LocalIndices()
    d match {
      case FData(name, paramTys, ty, cons) =>
        for paramTys <- paramTys.toTt
            _ <- summon[LocalIndices].withNames(paramTys.map(_.name)) {
              for ty <- ty.toTt
                  _ = ns.addDeclaration(name)
                  cons <- cons match {
                    case null => Right(null)
                    case cons : Seq[FConstructor] => {
                      ns.addDeclaration(name, cons.map(_.name))
                      cons.liftMap(_.toTt)
                    }
                  }
                  _ <- sb += PreData(ns.qn / name)(paramTys, ty, cons)
              yield ()
            }
        yield ()
      case FDataDef(name, cons) =>
        for data <- sb.getData(ns.qn / name)
            cons <- summon[LocalIndices].withNames(data.paramTys.map(_.name)) {
                      cons.liftMap(_.toTt)
                    }
            _ <- sb.updateData(ns.qn / name, cons)
        yield ns.addDeclaration(name, cons.map(_.name))
      case FRecord(name, paramTys, ty, fields) =>
        for paramTys <- paramTys.toTt
            _ <- summon[LocalIndices].withNames(paramTys.map(_.name) :+ "self") {
              for ty <- ty.toTt
                  _ = ns.addDeclaration(name)
                  fields <- fields match {
                    case null => Right(null)
                    case fields : Seq[FField] => fields.liftMap(_.toTt)
                  }
                  _ <- sb += PreRecord(ns.qn / name)(paramTys, ty, fields)
              yield ()
            }
        yield ()
      case FRecordDef(name, fields) =>
        for record <- sb.getRecord(ns.qn / name)
            fields <- summon[LocalIndices].withNames(record.paramTys.map(_.name) :+ "self") {
                        fields.liftMap(_.toTt)
                      }
            _ <- sb.updateRecord(ns.qn / name, fields)
        yield ()
      case FDefinition(name, ty, clauses) =>
        for ty <- ty.toTt
            _ = ns.addDeclaration(name)
            clauses <- clauses.liftMap(_.toTt)
            d = PreDefinition(ns.qn / name)(ty, clauses, null)
            _ <- sb += d
        yield ()
    }
  }
}