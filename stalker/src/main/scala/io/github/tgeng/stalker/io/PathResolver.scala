package io.github.tgeng.stalker.io

import java.lang.System

import java.io.File
import java.nio.file.Files
import scala.collection.mutable
import io.github.tgeng.stalker
import stalker.common._
import stalker.common.QualifiedName._
import io.github.tgeng.common.nullOps._

trait PathResolver(
  val sourceRoots : Seq[File],
  val fileCacheRoot : File,
  val signatureCacheRoot : File) {
  {
    // Clean up cache if it's for an old version
    import stalker.BuildInfo
    val buildId = BuildInfo.version + "." + BuildInfo.buildInfoBuildNumber
    def initCacheRoot(root: File) = {
      if (!root.exists) {
        root.mkDirsPlease
      }
      val buildIdFile = root / ".build_id"
      if (buildIdFile.exists) {
        if (buildIdFile.readAllText != buildId) {
          root.children.foreach(_.deleteRecursively)
          buildIdFile.writeAllText(buildId)
        }
      } else {
        buildIdFile.writeAllText(buildId)
      }
    }
    initCacheRoot(fileCacheRoot)
    initCacheRoot(signatureCacheRoot)
  }

  def resolveSourceFiles(qn: QualifiedName) : Seq[File] = resolveSourcePaths(qn).filter{ _.isFile }
  def resolveSourcePaths(qn: QualifiedName) : Seq[File] = sourceRoots.resolveSourceDirsImpl(qn.parts.reverse)

  private def (paths: Seq[File]) resolveSourceDirsImpl(names: List[String]) : Seq[File] = names match {
    case Nil => paths
    case name :: rest => paths
      .flatMap { d => 
        var result : List[File] = Nil
        val dir = d / name
        if (dir.isDirectory) result = dir :: result
        val file = d / s"$name.stalker"
        if (file.isFile) result = file :: result
        result
       }
      .resolveSourceDirsImpl(rest)
  }

  def resolveFileCacheFile(qn: QualifiedName) : File = qn match {
    case Root => fileCacheRoot / ".sfc"
    case parent / name => fileCacheRoot.resolveCacheDir(parent.parts.reverse) / s"$name.sfc"
  }

  def resolveSignatureCacheFile(qn: QualifiedName) : File = qn match {
    case Root => signatureCacheRoot / ".ssc"
    case parent / name => signatureCacheRoot.resolveCacheDir(parent.parts.reverse) / s"$name.ssc"
  }

  private def (path: File) resolveCacheDir(names: List[String]): File = names match {
    case Nil => path
    case name :: rest => (path / name).resolveCacheDir(rest)
  }
}

object PathResolver {
  private val userHome = File(System.getProperty("user.home"))
  private val sdk = sys.env.get("STALKER_SDK") match {
    case Some(d) => {
      val dir = File(d)
      if (!dir.isDirectory) throw IllegalStateException(s"Invalid SDK at $dir.")
      dir
    }
    case None => throw IllegalStateException("You must set the environment variable 'STALKER_SDK' in order to proceed.")
  }
  private val stdLibRoot = sdk / "stdlib"

  lazy val default = new PathResolver(
    { 
      sys.env.getOrElse("STALKER_SOURCE_ROOTS", "").split(File.pathSeparatorChar).filter(!_.isEmpty).map(File(_)).toSeq :+ File(".") :+ stdLibRoot
    },
    sys.env.get("STALKER_FILE_CACHE_ROOT") match {
      case Some(dir) => File(dir)
      case None => userHome / ".stalker/cache/file"
    },
    sys.env.get("STALKER_SIGNATURE_CACHE_ROOT") match {
      case Some(dir) => File(dir)
      case None => userHome / ".stalker/cache/signature"
    }
  ) {}

  def createTmp(sourceRoots: Seq[File]) = {
    val tmpRoot = Files.createTempDirectory("stalker-").toFile.!!
    new PathResolver(
        sourceRoots :+ stdLibRoot,
        tmpRoot / "cache/file",
        tmpRoot / "cache/signature/",
    ) {}
  }
}
