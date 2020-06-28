package io.github.tgeng.stalker.io

import java.io.File

import scala.collection.mutable

import io.github.tgeng.stalker
import stalker.common._
import stalker.core.fe._
import IoError._
import fileOps._
import timestampOps._

import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

class ModuleLoader(val pathResolver: PathResolver) {
  private val cache = mutable.Map[QualifiedName, Either[ParserError[Char], Module]]()

  def loadModule(qn: QualifiedName) : Either[ParserError[Char], Module] = cache.getOrElseUpdate(qn, {
    val sourceFiles = pathResolver.resolveSourceFiles(qn)
    sourceFiles.size match {
      case 0 => throw SourceFileNotFound(qn)
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
      case _ => throw DuplicatedSourceFile(qn, sourceFiles)
    }
  })

  private def loadFromSourceAndUpdateCache(sourceFile: File, cacheFile: File) : Either[ParserError[Char], Module] = {
    val fileContent = sourceFile.readAllText
    for module <- (parser.module << whitespaces << eof).parse(fileContent)
        _ = cacheFile.writeObject(module)
    yield module
  }

  private def loadFromCache(cacheFile: File) : Either[ParserError[Char], Module] = Right(cacheFile.readObject)
}