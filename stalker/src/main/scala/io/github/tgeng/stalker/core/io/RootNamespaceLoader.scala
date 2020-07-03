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
import Visibility._

import debug._

class RootNamespaceLoader(val moduleLoader: ModuleLoader) {
  private val pathResolver = moduleLoader.pathResolver
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
    try {
      for module <- moduleLoader.loadModule(qn)
          r <- module match {
            case Some(m) => 
              for ModuleNamespaces(privateNs, internalNs, publicNs) <- cache.getOrElseUpdate(qn, loadModuleNamespaces(qn, m)) 
              yield (requester == qn, requester hasPrefix qn.parent) match {
                case (true, _) => Some(privateNs)
                // Use the internal namespace if the requester is under the directory containing the module being imported.
                case (false, true) => Some(internalNs)
                case (false, false) => Some(publicNs)
              }
            case None => Right(None)
          }
      yield r
    } finally {
      importChain.remove(qn)
    }
  }

  private def loadModuleNamespaces(qn: QualifiedName, module: Module) : Result[ModuleNamespaces] = module match {
    case Module(commands) => {
      val privateNs = MutableNamespace(mutable.Set(NNamespace(builtins.namespace)))
      val internalNs = MutableNamespace()
      val publicNs = MutableNamespace()

      def getSrcNsElems(src: List[String]): Result[Set[NsElem]] =
        for rootNsOption <- loadNamespace(qn, QualifiedName.fromNames(src))
            localNsElems <- privateNs.resolve(src)
            srcNsElems = rootNsOption.map(NNamespace(_)).toSet | localNsElems
            r <- srcNsElems.isEmpty match {
              case false => Right(srcNsElems)
              case true => Left(UnresolvableNamespace(src))
            }
        yield r
      commands.foreach {
        case MDecl(decl, visibility) => {
          val declQn = NQualifiedName(qn / decl.name)
          privateNs(decl.name) add declQn
          visibility match {
            case Public => {
              internalNs(decl.name) add declQn
              publicNs(decl.name) add declQn
            }
            case Internal => internalNs(decl.name) add declQn
            case Private => ()
          }
        }
        case _ => ()
      }
      for {
        _ <- commands.liftMap {
          case MNsOp(src, dst, scope) =>
            for srcNsElems <- getSrcNsElems(src)
            yield scope match {
              case Private => privateNs(dst) addAll srcNsElems
              case Internal => internalNs(dst) addAll srcNsElems
              case Public => publicNs(dst) addAll srcNsElems
            }
          case _ => Right(())
        }
      } yield ModuleNamespaces(privateNs, internalNs, publicNs)
    }
  }
}

private case class ModuleNamespaces(privateNs: Namespace, internalNs: Namespace, publicNs: Namespace)

private class DirectoryNamespace(val rootNamespaceLoader: RootNamespaceLoader, requester: QualifiedName, val rootQn: QualifiedName) extends Namespace {
  override def renderImpl(qn: QualifiedName): Either[List[String], Unit] = {
    Left(((qn - rootQn) match {
      case Some(reversedNames) => reversedNames
      case _ => qn.parts
    }).reverse)
  }

  override def resolveImpl(names: List[String]): Result[Set[NsElem]] = names match {
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
