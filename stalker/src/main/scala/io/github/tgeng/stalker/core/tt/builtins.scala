package io.github.tgeng.stalker.core.tt

import io.github.tgeng.stalker.common._
import io.github.tgeng.stalker.core.common.Error._
import io.github.tgeng.common.eitherOps._

import QualifiedName._
import Declaration._
import PreDeclaration._
import Term._
import Whnf._
import Pattern._
import CoPattern._
import CaseTree._
import UncheckedRhs._

object builtins {
  private val parent = Root / "stalker" / "builtins"

  val levelType: PreDefinition = new PreDefinition(parent / "Level")(
    TWhnf(WType(TWhnf(lconst(0)))),
    Seq(UncheckedClause(
      Nil,
      UTerm(TWhnf(WLevel)),
    ))
  )

  val typeType: PreDefinition = new PreDefinition(parent / "Type")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevel), TWhnf(WType(TWhnf(lsuc(TWhnf(WVar(0, Nil)))))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(0)("l"))),
      UTerm(TWhnf(WType(TWhnf(WVar(0, Nil))))),
    ))
  )
  
  val lsucFn: PreDefinition = new PreDefinition(parent / "lsuc")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevel), TWhnf(WLevel))),
    Seq(UncheckedClause(
      List(QPattern(PVar(0)("l"))),
      UTerm((TWhnf(lsuc(TWhnf(WVar(0, Nil)))))),
    ))
  )

  val lmaxFn: PreDefinition = new PreDefinition(parent / "lmax")(
    TWhnf(WFunction("l1" ∷ TWhnf(WLevel), TWhnf(WFunction("l2" ∷ TWhnf(WLevel), TWhnf(WLevel))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(1)("l1")), QPattern(PVar(0)("l2"))),
      UTerm(TWhnf(lmax(TWhnf(WVar(1, Nil)), TWhnf(WVar(0, Nil))))),
    ))
  )

  val idType: PreDefinition = new PreDefinition(parent / "Id")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevel), TWhnf(WFunction("A" ∷ TWhnf(WType(TWhnf(WVar(0, Nil)))), TWhnf(WFunction("x" ∷ TWhnf(WVar(0, Nil)), TWhnf(WFunction("y" ∷ TWhnf(WVar(1, Nil)), TWhnf(WType(TWhnf(WVar(3, Nil)))))))))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(3)("l")), QPattern(PVar(2)("A")), QPattern(PVar(1)("x")), QPattern(PVar(0)("y"))),
      UTerm(TWhnf(WId(TWhnf(WVar(3, Nil)), TWhnf(WVar(2, Nil)), TWhnf(WVar(1, Nil)), TWhnf(WVar(0, Nil))))),
    ))
  )

  val signature = {
    val sb = SignatureBuilder.create(EmptySignature)
    sb ++= sb.elaborate(levelType).!!!
    sb ++= sb.elaborate(typeType).!!!
    sb ++= sb.elaborate(lsucFn).!!!
    sb ++= sb.elaborate(lmaxFn).!!!
    sb ++= sb.elaborate(idType).!!!
    sb
  }

  val namespace = {
    import NsElem._
    val ns = MutableNamespace()
    def add(d: PreDeclaration) = {
      ns(d.qn.parts.reverse).add(NQualifiedName(d.qn))
    }
    add(levelType)
    add(typeType)
    add(lsucFn)
    add(lmaxFn)
    add(idType)
    ns.seal
  }
}
