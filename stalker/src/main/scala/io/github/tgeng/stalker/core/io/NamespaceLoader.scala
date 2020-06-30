package io.github.tgeng.stalker.core.io

import java.io.File
import scala.collection.mutable

import io.github.tgeng.stalker
import stalker.common._
import stalker.core.fe._

class NamespaceLoader(moduleLoader: ModuleLoader, pathResolver: PathResolver) {
  private val importChain = mutable.LinkedHashSet[QualifiedName]()
  private val cache = mutable.HashMap[QualifiedName, (Namespace, Namespace)]()

  def loadNamespace(qn: QualifiedName) : Namespace = {
    ???
  }

  private def loadModuleNamespace(qn: QualifiedName) : Namespace = {
    ???
  }

  private def loadModuleNamespace(module: Module) : ModuleNamespaces = {
    ???
  }

  private def loadDirectoryNamespace(qn: QualifiedName) : Namespace = DirectoryNamespace(qn)
}

private case class ModuleNamespaces(internal: Namespace, external: Namespace)

private class DirectoryNamespace(val rootQn: QualifiedName) extends Namespace {
  override def renderImpl(qn: QualifiedName): Either[List[String], Unit] = {
    Left(((qn - rootQn) match {
      case Some(reversedNames) => reversedNames
      case _ => qn.parts
    }).reverse)
  }

  protected def resolveImpl(names: List[String]): Set[NsElem] = names match {
    case _ => ???
  }
}
