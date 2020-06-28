package io.github.tgeng.stalker.io

import java.io.File
import io.github.tgeng.stalker._
import common.QualifiedName

opaque type Timestamp = Long

extension timestampOps on (t1: Timestamp) {
  def < (t2: Timestamp) = t1 < t2
  def > (t2: Timestamp) = t1 > t2
  def <= (t2: Timestamp) = t1 <= t2
  def >= (t2: Timestamp) = t1 >= t2
}

extension fileTimestampOps on (f: File) {
  def timestamp : Option[Timestamp] = f.lastModified match {
    case 0 => None
    case t => Some(t)
  }
 }