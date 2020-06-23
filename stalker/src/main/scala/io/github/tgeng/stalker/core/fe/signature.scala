package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import scala.collection.Seq
import io.github.tgeng.common.eitherOps._
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.common.QualifiedName._
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.tt.Namespace
import io.github.tgeng.stalker.core.tt.MutableNamespace
import io.github.tgeng.stalker.core.tt.LeafNamespace
import io.github.tgeng.stalker.core.tt._

import MutableNamespace.{_, given _}

enum FDeclaration {
  case FData(name: String, paramTys: FTelescope, ty: FTerm, cons: Seq[FConstructor])
  case FRecord(name: String, paramTys: FTelescope, ty: FTerm, fields: Seq[FField])
  case FDefinition(name: String, ty: FTerm, clauses: Seq[FUncheckedClause])

  override def toString = this match {
    case FData(name, paramTys ,ty, cons) => s"""FData("$name", $paramTys, $ty, $cons)"""
    case FRecord(name, paramTys ,ty, fields) => s"""FRecord("$name", $paramTys, $ty, $fields)"""
    case FDefinition(name, ty, clauses) => s"""FDefinition("$name", $ty, $clauses)"""
  }

  def toNamespace(qn: QualifiedName) : Namespace = this match {
    case FData(name, _, _, cons) => {
      val ns = MutableNamespace.create(qn)
      cons.foreach(con => ns(con.name) = LeafNamespace(qn / con.name))
      ns
    }
    case FRecord(name, _, _, _) => LeafNamespace(qn / name)
    case FDefinition(name, _, _) => LeafNamespace(qn / name)
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

import PreDeclaration._
import FDeclaration._
import FUncheckedRhs._
import UncheckedRhs._

object FSignatureBuilder {
  def create = FSignatureBuilder()
}

  // TODO: remove this class
class FSignatureBuilder extends Signature {
  import ftConversion.{given _, _}
  private val sb = SignatureBuilder.create(builtins.signature)

  export sb.getData
  export sb.getRecord
  export sb.getDefinition
  export sb.declarations

  def += (d: FDeclaration)(using ns: MutableNamespace) : Result[Unit] = {
    given LocalIndices = LocalIndices()
    d match {
      case FData(name, paramTys, ty, cons) =>
        for paramTys <- paramTys.toTt
            _ <- summon[LocalIndices].withNames(paramTys.map(_.name)) {
              for ty <- ty.toTt
                  _ = ns.addDeclaration(name)
                  cons <- cons match {
                    case cons : Seq[FConstructor] => {
                      ns.addDeclaration(name, cons.map(_.name))
                      cons.liftMap(_.toTt)
                    }
                  }
              yield sb ++= sb.elaborate(PreData(ns.qn / name)(paramTys, ty, cons)).!!!
            }
        yield ()
      case FRecord(name, paramTys, ty, fields) =>
        for paramTys <- paramTys.toTt
            _ <- summon[LocalIndices].withNames(paramTys.map(_.name) :+ "self") {
              for ty <- ty.toTt
                  _ = ns.addDeclaration(name)
                  fields <- fields match {
                    case fields : Seq[FField] => fields.liftMap(_.toTt)
                  }
              yield sb ++= sb.elaborate(PreRecord(ns.qn / name)(paramTys, ty, fields)).!!!
            }
        yield ()
      case FDefinition(name, ty, clauses) =>
        for ty <- ty.toTt
            _ = ns.addDeclaration(name)
            clauses <- clauses.liftMap(_.toTt)
            d = PreDefinition(ns.qn / name)(ty, clauses)
        yield sb ++= sb.elaborate(d).!!!
    }
  }
}