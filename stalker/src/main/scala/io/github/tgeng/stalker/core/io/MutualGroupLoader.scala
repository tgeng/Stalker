package io.github.tgeng.stalker.core.io

import scala.collection.mutable
import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker
import stalker.common._
import Error._
import QualifiedName._
import stalker.core
import core.fe._
import core.tt._
import ftConversion.{given _}
import depAnalysis._
import ModuleCommand._

import debug._

class MutualGroupLoader(val rootNamespaceLoader: RootNamespaceLoader) {

  private val moduleLoader = rootNamespaceLoader.moduleLoader
  private val moduleCache = mutable.Map[QualifiedName, Result[Seq[MutualGroup]]]()
  private val defCache = mutable.Map[QualifiedName, Result[MutualGroup]]()

  def loadMutualGroups(moduleQn: QualifiedName) : Result[Seq[MutualGroup]] = moduleCache.getOrElseUpdate(moduleQn, {
    for {
      moduleOption <- moduleLoader.loadModule(moduleQn)
      namespaceOption <- rootNamespaceLoader.loadNamespace(moduleQn, moduleQn)
      r <- (moduleOption, namespaceOption) match {
        case (Some(module), Some(namespace)) => {
          val decls = module.commands.collect{ case MDecl(decl, _) => decl }
          for {
            preDecls <- decls.liftMap{_.toTt(moduleQn)(using namespace)}
          } yield analyzeMutualDependency(preDecls.toSet)
        }
        case _ => Left(UnresolvableModuleError(moduleQn))
      }
    } yield r
  })

  def loadContainingMutualGroup(defQn: QualifiedName) : Result[MutualGroup] = {
    defCache.get(defQn) match {
      case Some(r) => return r
      case _ => {
        for {
          moduleMutualGroups <- loadMutualGroups(defQn.parent)
          _ = moduleMutualGroups.foreach { mutualGroup => 
            mutualGroup.declarations.foreach { decl =>
              defCache(decl.qn) = Right(mutualGroup)
            }
          }
          r <- defCache.get(defQn) match {
            case Some(r) => r
            case _ => Left(MissingDefinitionError(defQn))
          }
        } yield r
      }
    }
  }
}