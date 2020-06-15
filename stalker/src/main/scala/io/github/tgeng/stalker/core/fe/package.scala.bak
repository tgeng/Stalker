package io.github.tgeng.stalker.core.fe

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker.common.QualifiedName
import io.github.tgeng.stalker.core.common.Namespace
import io.github.tgeng.stalker.core.common.MutableNamespace
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.stalker.core.fe._
import io.github.tgeng.stalker.core.tt._
import FDeclaration._
import QualifiedName._

class Package(ns: Namespace, sg: Signature) extends Namespace with Signature {
  export ns.get
  export ns.qn
  export ns.constructorName
  export ns.iterator
  export sg.getData
  export sg.getRecord
  export sg.getDefinition
  export sg.allDeclarations
}

enum PackageCommand {
  case PImport(names: Seq[String], merge: Boolean)
  case PDecl(decl: FDeclaration)
  case PExport(names: Seq[String])
}
import PackageCommand._

object Package {

  def create(qn: QualifiedName, commands: Seq[PackageCommand])(using pr: PackageResolver) : Result[Package] = {
    val innerNs = MutableNamespace.createWithBuiltins(qn)
    val exportNs = MutableNamespace.create(qn)
    given MutableNamespace = innerNs
    given Namespace = innerNs
    val sb = SignatureBuilder.create
    given SignatureBuilder = sb
    for _ <- commands.liftMap(c => processCommand(c, exportNs))
    yield Package(exportNs, sb)
  }

  private def processCommand(c: PackageCommand, exportNs: MutableNamespace)(using ns: MutableNamespace, sb: SignatureBuilder, pr: PackageResolver) : Result[Unit] = c match {
    case PImport(names, merge) => ???
    case PDecl(d) => addDeclaration(d)
    case PExport(names) => ???
  }

  def addDeclaration(d: FDeclaration)(using ns: MutableNamespace, sb: SignatureBuilder) : Result[Unit] = {
    import ftConversion.{given _, _}
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
                    case _ => throw AssertionError("suppress dotty bug")
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
                    case _ => throw AssertionError("suppress dotty bug")
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
