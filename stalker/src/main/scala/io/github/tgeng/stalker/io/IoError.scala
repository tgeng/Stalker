package io.github.tgeng.stalker.io

import java.io.File
import io.github.tgeng.stalker
import stalker.common._

enum IoError extends Throwable {
  case SourceFileNotFound(qn: QualifiedName)
  case DuplicatedSourceFile(qn: QualifiedName, val sourceFiles: Seq[File])
  case QualifiedNameNotFound(containingFileQn: QualifiedName, qn: QualifiedName)
} 
