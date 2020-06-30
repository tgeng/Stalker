package io.github.tgeng.stalker.core.io

import java.io.File

import scala.collection.mutable

import io.github.tgeng.common.fileOps
import io.github.tgeng.common.timestampOps
import io.github.tgeng.stalker
import stalker.common._
import stalker.common.Error._
import stalker.core.fe._

import io.github.tgeng.parse._
import io.github.tgeng.parse.string.{given _, _}

class ModuleLoader(val pathResolver: PathResolver) {
  private val cache = mutable.Map[QualifiedName, Result[Option[Module]]]()

  def loadModule(qn: QualifiedName) : Result[Option[Module]] = cache.getOrElseUpdate(qn, {
    for sourceFile <- pathResolver.resolveSourceFile(qn)
        r <- sourceFile match {
          case None => Right(None)
          case Some(sourceFile) => {
            val sourceTimestamp = sourceFile.timestamp
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
        }
    yield r
  })

  private def loadFromSourceAndUpdateCache(sourceFile: File, cacheFile: File) : Result[Option[Module]] = {
    val fileContent = sourceFile.readAllText
    (for module <- (parser.module << whitespaces << eof).parse(fileContent)
        _ = cacheFile.writeObject(module)
    yield Some(module)).left.map(ParsingError(_))
  }

  private def loadFromCache(cacheFile: File) : Result[Option[Module]] = Right(cacheFile.readObject)
}