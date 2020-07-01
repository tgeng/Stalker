package io.github.tgeng.stalker.core.io

import scala.language.implicitConversions
import io.github.tgeng.common.eitherOps
import io.github.tgeng.common.optionOps
import io.github.tgeng.testing.UnitSpec
import io.github.tgeng.stalker
import stalker.common.QualifiedName.{given _, _}
import stalker.core.fe.ModuleCommand._
import stalker.common._
import NsElem._

class RootNamespaceLoaderSpec extends UnitSpec {
  val pathResolver = PathResolver.createTmp(Nil)
  val moduleLoader = ModuleLoader(pathResolver)
  val nsLoader = RootNamespaceLoader(moduleLoader, pathResolver)

  "stalker.data.nat.base internal namespace" in {
    val internalNs = nsLoader.loadNamespace("stalker.data.nat.base", "stalker.data.nat.base").!!!.!!!
    assert(internalNs.resolve("Nat").!!! == Set(NQualifiedName("stalker.data.nat.base.Nat")))
  }
}