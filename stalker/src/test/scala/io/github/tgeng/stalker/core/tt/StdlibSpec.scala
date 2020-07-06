package io.github.tgeng.stalker.core.tt

import scala.language.implicitConversions
import io.github.tgeng.common.eitherOps
import io.github.tgeng.stalker
import stalker.core.testing._
import stalker.core.fe.builders._

class StdlibSpec extends CoreSpec {
  signatureLoader.loadSignature("stalker.data.vector.base").!!!
}