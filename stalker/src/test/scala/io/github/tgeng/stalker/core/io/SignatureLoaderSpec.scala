package io.github.tgeng.stalker.core.io

import scala.language.implicitConversions
import io.github.tgeng.stalker
import stalker.core.testing._
import stalker.core.fe.builders._

class SignatureLoaderSpec extends CoreSpec {
  withSignature("io.github.tgeng.stalker.core.io.basic") {
    "basic typing" in {
      t"unit" ∷ t"Unit"
    }
  }
}