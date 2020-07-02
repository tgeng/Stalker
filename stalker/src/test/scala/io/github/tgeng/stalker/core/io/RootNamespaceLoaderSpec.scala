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

  "stalker.data.nat.base private namespace" in {
    val privateNs = nsLoader.loadNamespace("stalker.data.nat.base", "stalker.data.nat.base").!!!.!!!
    assert(privateNs.resolve("Nat").!!! == Set(NQualifiedName("stalker.data.nat.base.Nat")))
    assert(privateNs.resolve("stalker", "builtins", "Level").!!! == Set(NQualifiedName("stalker.builtins.Level")))
    assert(privateNs.resolve("stalker", "builtins", "Type").!!! == Set(NQualifiedName("stalker.builtins.Type")))
    assert(privateNs.resolve("stalker", "builtins", "lsuc").!!! == Set(NQualifiedName("stalker.builtins.lsuc")))
    assert(privateNs.resolve("stalker", "builtins", "lmax").!!! == Set(NQualifiedName("stalker.builtins.lmax")))
    assert(privateNs.resolve("stalker", "builtins", "Id").!!! == Set(NQualifiedName("stalker.builtins.Id")))
  }

  "stalker.data.nat.base internal namespace" in {
    val internalNs = nsLoader.loadNamespace("stalker.data.nat.foo", "stalker.data.nat.base").!!!.!!!
    assert(internalNs.resolve("Nat").!!! == Set(NQualifiedName("stalker.data.nat.base.Nat")))
    assert(internalNs.resolve("stalker", "builtins", "Level").!!! == Set())
  }

  "stalker.data.nat.base external namespace" in {
    val externalNs = nsLoader.loadNamespace("stalker.data.bar", "stalker.data.nat.base").!!!.!!!
    assert(externalNs.resolve("Nat").!!! == Set(NQualifiedName("stalker.data.nat.base.Nat")))
    assert(externalNs.resolve("stalker", "builtins", "Level").!!! == Set())
  }
}