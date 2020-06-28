package io.github.tgeng.stalker.io

import io.github.tgeng.stalker
import stalker.common._
import stalker.core.fe._

class DiskNamespace(val rootQn: QualifiedName) extends Namespace {
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
