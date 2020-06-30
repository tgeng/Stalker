package io.github.tgeng.stalker.core.io

import java.io.File
import io.github.tgeng.common.nullOps._
import io.github.tgeng.stalker._
import core.fe._

enum DeclType {
  case Data
  case Record
  case Definition
}

enum SourceTree {
  case SourceFile(file: File)
  case SourceDir(subTrees: Map[String, SourceTree])
}

import SourceTree._

def (sd: SourceDir) resolveDir(name: String) : Option[SourceDir] = sd.subTrees.get(name).collect{
  case d: SourceDir => d
}

def (sd: SourceDir) resolveFile(name: String) : Option[SourceFile] = sd.subTrees.get(name + ".stalker").collect{
  case f: SourceFile => f
}
