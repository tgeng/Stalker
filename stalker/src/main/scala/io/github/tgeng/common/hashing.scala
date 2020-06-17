package io.github.tgeng.common

import java.security.MessageDigest
import serialization._

object hashing {
  private val hasher = MessageDigest.getInstance("SHA-256").!!

  def hash(values: Serializable*) : Array[Byte] = {
    for (value <- values) {
      hasher.update(value.serialize)
    }
    hasher.digest.!!
  }
}