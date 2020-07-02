package io.github.tgeng.common

import java.io.File

object sourceUtils {
  inline def thisFile : File = File(thisFilePath)
  inline def thisFilePath : String = ${
    thisFileImpl 
  }

  import scala.quoted._
  
  private def thisFileImpl(using qctx: QuoteContext) : Expr[String] = {
    import qctx.tasty._
    Literal(Constant(qctx.tasty.rootPosition.sourceFile.jpath.toString)).seal.asInstanceOf[Expr[String]]
  }
}
