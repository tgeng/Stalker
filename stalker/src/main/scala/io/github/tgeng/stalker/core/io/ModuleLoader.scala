package io.github.tgeng.stalker.core.io

import java.io.File

import scala.collection.mutable

import io.github.tgeng.common.fileOps
import io.github.tgeng.stalker
import stalker.common._
import stalker.core.common.Error._
import stalker.core.fe._

import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

class ModuleLoader(val pathResolver: PathResolver) {
  private val cache = mutable.Map[QualifiedName, Result[Option[Module]]]()

  def loadModule(qn: QualifiedName) : Result[Option[Module]] = cache.getOrElseUpdate(qn, {
    val sourceFiles = pathResolver.resolveSourceFiles(qn)
    sourceFiles.size match {
      case 0 => Right(None)
      case 1 => {
        val sourceFile = sourceFiles.head
        val sourceTimestamp = sourceFiles.head.timestamp
        val cacheFile = pathResolver.resolveModuleCacheFile(qn)
        val cacheTimestamp = cacheFile.timestamp
        if (sourceTimestamp >= cacheTimestamp) {
          // cache is stale
          loadFromSourceAndUpdateCache(sourceFile, cacheFile)
        } else {
          // cache is good
          loadFromCache(cacheFile)
        }
      }
      case _ => Left(DuplicatedSourceFile(qn, sourceFiles))
    }
  })

  private def loadFromSourceAndUpdateCache(sourceFile: File, cacheFile: File) : Result[Option[Module]] = {
    val fileContent = sourceFile.readAllText
    (for module <- (parser.module << whitespaces << eof).parse(fileContent)
        _ = cacheFile.writeObject(module)
    yield Some(module)).left.map(ParsingError(_))
  }

  private def loadFromCache(cacheFile: File) : Result[Option[Module]] = Right(cacheFile.readObject)
}