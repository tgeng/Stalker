package io.github.tgeng.stalker.io

import java.io.File
import io.github.tgeng.stalker._
import common.QualifiedName

case class FileStats (
  val timestamp: Long,
)

object FileStats {
  def loadFileStats(root: File)(qn: QualifiedName): Option[FileStats] = ???
}