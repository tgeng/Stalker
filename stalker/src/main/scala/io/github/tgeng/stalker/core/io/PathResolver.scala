package io.github.tgeng.stalker.core.io

import java.lang.System

import java.io.File
import java.nio.file.Files
import scala.collection.mutable
import io.github.tgeng.common._
import io.github.tgeng.common.fileOps
import io.github.tgeng.common.nullOps._
import io.github.tgeng.stalker
import stalker.common._
import stalker.common.QualifiedName._
import stalker.common.Error._
import SourceTree._

trait PathResolver(
  val sourceRoots : Seq[File],
  val moduleCacheRoot : File,
  val signatureCacheRoot : File) {

  private val sourceTrees : Seq[SourceTree] = sourceRoots.flatMap(convertFileToSourceTree)

  private def convertFileToSourceTree(file: File) : Option[SourceTree] = file match {
    case file if (file.getName.!!.endsWith(".stalker") && file.isFile) => Some(SourceFile(file))
    case dir if (dir.isDirectory) => {
      val subTrees = dir.children.map((k, v) => convertFileToSourceTree(v).map{(k, _)}).flatten.toMap
      if (subTrees.isEmpty) None
      else Some(SourceDir(subTrees))
    }
    case _ => None
  }

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
          root.children.foreach((_, f) => f.deleteRecursively)
          buildIdFile.writeAllText(buildId)
        }
      } else {
        buildIdFile.writeAllText(buildId)
      }
    }
    initCacheRoot(moduleCacheRoot)
    initCacheRoot(signatureCacheRoot)
  }

  def resolveSourceFile(qn: QualifiedName) : Result[Option[File]] = resolveSourceFiles(qn).toList match {
    case Nil => Right(None)
    case f :: Nil => Right(Some(f))
    case sources => Left(DuplicatedSourceFile(qn, sources))
  }

  private def resolveSourceFiles(qn: QualifiedName) : Seq[File] = sourceTrees.resolveSourcePathsImpl(qn.parts.reverse).collect{
    case SourceFile(f) => f
  }

  def resolveSourceDirs(qn: QualifiedName) : Seq[SourceDir] = sourceTrees.resolveSourcePathsImpl(qn.parts.reverse).collect{
    case d : SourceDir => d
  }

  private def (trees: Seq[SourceTree]) resolveSourcePathsImpl(names: List[String]) : Seq[SourceTree] = names match {
    case Nil => trees
    case name :: rest => trees
      .flatMap {
        case _ : SourceFile => Nil
        case d: SourceDir => Seq(d.resolveFile(name), d.resolveDir(name)).flatten
      }
      .resolveSourcePathsImpl(rest)
  }

  def resolveModuleCacheFile(qn: QualifiedName) : File = qn match {
    case Root => moduleCacheRoot / ".smc"
    case parent / name => moduleCacheRoot.resolveCacheDir(parent.parts.reverse) / s"$name.smc"
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
      case None => userHome / ".stalker/cache/module"
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
        tmpRoot / "cache/module",
        tmpRoot / "cache/signature/",
    ) {}
  }
}
