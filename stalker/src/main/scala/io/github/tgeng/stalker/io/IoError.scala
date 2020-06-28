package io.github.tgeng.stalker.io

import io.github.tgeng.stalker
import stalker.common._

enum IoError extends Throwable {
  case SourceFileNotFound(qn: QualifiedName)
  case QualifiedNameNotFound(containingFileQn: QualifiedName, qn: QualifiedName)
} 
