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

import debug._

class RootNamespaceLoaderSpec extends UnitSpec {
  val pathResolver = PathResolver.createTmp(Nil)
  val moduleLoader = ModuleLoader(pathResolver)
  val nsLoader = RootNamespaceLoader(moduleLoader)

  "stalker.data.nat.base private namespace" in {
    val privateNs = nsLoader.loadNamespace("stalker.data.nat.base", "stalker.data.nat.base").!!!.!!!
    assert(privateNs.resolveQn("Nat").!!! == Set[QualifiedName]("stalker.data.nat.base.Nat"))
    assert(privateNs.resolveQn("stalker", "builtins", "Level").!!! == Set[QualifiedName]("stalker.builtins.Level"))
    assert(privateNs.resolveQn("stalker", "builtins", "Type").!!! == Set[QualifiedName]("stalker.builtins.Type"))
    assert(privateNs.resolveQn("stalker", "builtins", "lsuc").!!! == Set[QualifiedName]("stalker.builtins.lsuc"))
    assert(privateNs.resolveQn("stalker", "builtins", "lmax").!!! == Set[QualifiedName]("stalker.builtins.lmax"))
    assert(privateNs.resolveQn("stalker", "builtins", "Id").!!! == Set[QualifiedName]("stalker.builtins.Id"))
  }

  "stalker.data.nat.base internal namespace" in {
    val internalNs = nsLoader.loadNamespace("stalker.data.nat.foo", "stalker.data.nat.base").!!!.!!!
    assert(internalNs.resolveQn("Nat").!!! == Set[QualifiedName]("stalker.data.nat.base.Nat"))
    assert(internalNs.resolveQn("stalker", "builtins", "Level").!!! == Set())
  }

  "stalker.data.nat.base external namespace" in {
    val externalNs = nsLoader.loadNamespace("stalker.data.bar", "stalker.data.nat.base").!!!.!!!
    assert(externalNs.resolveQn("Nat").!!! == Set[QualifiedName]("stalker.data.nat.base.Nat"))
    assert(externalNs.resolveQn("stalker", "builtins", "Level").!!! == Set())
  }
}