package io.github.tgeng.stalker.io

import io.github.tgeng.common.nullOps._
import io.github.tgeng.stalker._
import core.fe._

enum DeclType {
  case Data
  case Record
  case Definition
}

enum PackageCommand {
  case PImport(names: Seq[String], merge: Boolean)
  case PExport(names: Seq[String], merge: Boolean)
  case PDecl(decl: FDeclaration)
}
