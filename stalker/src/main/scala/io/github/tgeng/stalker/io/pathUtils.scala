package io.github.tgeng.stalker.io

import java.io.File
import scala.collection.mutable
import io.github.tgeng.stalker
import stalker.common._
import stalker.common.QualifiedName._

object Paths {
  val sourceRoots : Seq[File] = sys.env("STALKER_SOURCE_ROOTS").split(File.pathSeparatorChar).map(File(_)).toSeq
  val fileCacheRoot : File = File(sys.env("STALKER_FILE_CACHE_ROOT"))
  val signatureCacheRoot : File = File(sys.env("STALKER_FILE_CACHE_ROOT"))

  def resolveSourceFiles(qn: QualifiedName) : Seq[File] = resolveSourcePaths(qn).filter{ _.isFile }
  def resolveSourcePaths(qn: QualifiedName) : Seq[File] = sourceRoots.resolveSourceDirsImpl(qn.parts.reverse)

  private def (paths: Seq[File]) resolveSourceDirsImpl(names: List[String]) : Seq[File] = names match {
    case Nil => paths
    case name :: rest => paths
      .flatMap { d => 
        var result : List[File] = Nil
        val dir = File(d, name)
        if (dir.isDirectory) result = dir :: result
        val file = File(d, s"$name.stalker")
        if (file.isFile) result = file :: result
        result
       }
      .resolveSourceDirsImpl(rest)
  }

  def resolveFileCacheFile(qn: QualifiedName) : File = qn match {
    case Root => File(fileCacheRoot, ".sfc")
    case parent / name => File(fileCacheRoot.resolveCacheDir(parent.parts.reverse), s"$name.sfc")
  }

  def resolveSigCacheFile(qn: QualifiedName) : File = qn match {
    case Root => File(signatureCacheRoot, ".ssc")
    case parent / name => File(signatureCacheRoot.resolveCacheDir(parent.parts.reverse), s"$name.ssc")
  }

  private def (path: File) resolveCacheDir(names: List[String]): File = names match {
    case Nil => path
    case name :: rest => File(path, name).resolveCacheDir(rest)
  }
}