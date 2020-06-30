package io.github.tgeng.stalker.core.io

import java.io.File
import scala.language.implicitConversions
import scala.collection.immutable
import scala.collection.mutable
import scala.collection.Set

import io.github.tgeng.common.extraSeqOps
import io.github.tgeng.stalker
import stalker.common._
import QualifiedName._
import stalker.core.fe._
import stalker.core.tt._
import stalker.common.Error._
import SourceTree._
import NsElem._
import ModuleCommand._

class RootNamespaceLoader(moduleLoader: ModuleLoader, pathResolver: PathResolver) {
  private val importChain = mutable.LinkedHashSet[QualifiedName]()
  private val cache = mutable.HashMap[QualifiedName, Result[ModuleNamespaces]]()

  def loadNamespace(requester: QualifiedName, qn: QualifiedName) : Result[Option[Namespace]] = {
    for moduleNamespace <- loadModuleNamespace(requester, qn)
        directoryNamespace <- loadDirectoryNamespace(requester, qn)
    yield {
      val resultNamespaces = immutable.Set(moduleNamespace, directoryNamespace).flatten
      if (resultNamespaces.isEmpty) None
      else Some(ImmutableNamespace(resultNamespaces.map(NsElem.NNamespace(_)), Map.empty))
    }
  }

  private def loadDirectoryNamespace(requester: QualifiedName, qn: QualifiedName) : Result[Option[Namespace]] = {
    if (pathResolver.resolveSourceDirs(qn).isEmpty) Right(None)
    else Right(Some(DirectoryNamespace(this, requester, qn)))
  }

  private def loadModuleNamespace(requester: QualifiedName, qn: QualifiedName) : Result[Option[Namespace]] = {
    if (importChain.contains(qn)) {
      return Left(CyclicImport(importChain.dropWhile(_ != qn).toSeq))
    }
    importChain.add(qn)
    val r = for module <- moduleLoader.loadModule(qn)
        r <- module match {
          case Some(m) => 
            for ModuleNamespaces(internal, external) <- cache.getOrElseUpdate(qn, loadModuleNamespaces(qn, m)) 
            yield requester isPrefixedWith qn match {
              // Use the internal namespace if the requester is under the module being imported.
              case true => Some(internal)
              case false => Some(external)
            }
          case None => Right(None)
        }
    yield r
    importChain.dropRight(1)
    r
  }

  private def loadModuleNamespaces(qn: QualifiedName, module: Module) : Result[ModuleNamespaces] = module match {
    case Module(commands) => {
      val internalNs = MutableNamespace(mutable.Set(NNamespace(builtins.namespace)))
      val externalNs = MutableNamespace()

      def getSrcNsElems(src: List[String]): Result[Set[NsElem]] =
        for rootNsOption <- loadNamespace(qn, QualifiedName.fromNames(src))
            localNsElems <- internalNs.resolve(src)
            srcNsElems = rootNsOption.map(NNamespace(_)).toSet | localNsElems
            r <- srcNsElems.isEmpty match {
              case false => Right(srcNsElems)
              case true => Left(UnresolvableNamespace(src))
            }
        yield r

      for {
        _ <- commands.liftMap {
          case MImport(src, dst, shouldExport) =>
            for srcNsElems <- getSrcNsElems(src)
            yield {
              internalNs(dst) addAll srcNsElems
              if (shouldExport) externalNs(dst) addAll srcNsElems
            }
          case MExport(src, dst) =>
            for srcNsElems <- getSrcNsElems(src)
            yield externalNs(dst) addAll srcNsElems
          case MDecl(decl, shouldExport) => {
            val declQn = NQualifiedName(qn / decl.name)
            internalNs(decl.name) add declQn
            if (shouldExport) externalNs(decl.name) add declQn
            Right(())
          }
        }
      } yield ModuleNamespaces(internalNs, externalNs)
    }
  }
}

private case class ModuleNamespaces(internal: Namespace, external: Namespace)

private class DirectoryNamespace(val rootNamespaceLoader: RootNamespaceLoader, requester: QualifiedName, val rootQn: QualifiedName) extends Namespace {
  override def renderImpl(qn: QualifiedName): Either[List[String], Unit] = {
    Left(((qn - rootQn) match {
      case Some(reversedNames) => reversedNames
      case _ => qn.parts
    }).reverse)
  }

  protected def resolveImpl(names: List[String]): Result[Set[NsElem]] = names match {
    case Nil => Right(Set(NsElem.NNamespace(this)))
    case name :: rest => 
      for namespaceOption <- rootNamespaceLoader.loadNamespace(requester, rootQn / name)
          r <- namespaceOption match {
            case Some(ns) => ns.resolve(rest)
            case None => Right(Set.empty[NsElem])
          }
      yield r
  }
}
