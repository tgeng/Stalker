package io.github.tgeng.stalker.core.tt

import io.github.tgeng.stalker.common.QualifiedName._

import DeclarationT._
import Term._
import Whnf._
import ClauseT._
import Pattern._
import CoPattern._
import CaseTree._
import UncheckedRhs._

object builtins {
  private val parent = Root / "stalker" / "builtins"

  val levelType: PreDefinition = new DefinitionT(parent / "Level")(
    TWhnf(WType(TWhnf(lconst(0)))),
    Seq(UncheckedClause(
      Nil,
      UTerm(TWhnf(WLevelType)),
    )), 
    null
  )

  val typeType: PreDefinition = new DefinitionT(parent / "Type")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevelType), TWhnf(WType(TWhnf(lsuc(TWhnf(WVar(0, Nil)))))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(0)("l"))),
      UTerm(TWhnf(WType(TWhnf(WVar(0, Nil))))),
    )),
    null
  )
  
  val lsucFn: PreDefinition = new DefinitionT(parent / "lsuc")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevelType), TWhnf(WLevelType))),
    Seq(UncheckedClause(
      List(QPattern(PVar(0)("l"))),
      UTerm((TWhnf(lsuc(TWhnf(WVar(0, Nil)))))),
    )),
    null
  )

  val lmaxFn: PreDefinition = new DefinitionT(parent / "lmax")(
    TWhnf(WFunction("l1" ∷ TWhnf(WLevelType), TWhnf(WFunction("l2" ∷ TWhnf(WLevelType), TWhnf(WLevelType))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(1)("l1")), QPattern(PVar(0)("l2"))),
      UTerm(TWhnf(lmax(TWhnf(WVar(1, Nil)), TWhnf(WVar(0, Nil))))),
    )),
    null
  )

  val idType: PreDefinition = new DefinitionT(parent / "Id")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevelType), TWhnf(WFunction("A" ∷ TWhnf(WType(TWhnf(WVar(0, Nil)))), TWhnf(WFunction("x" ∷ TWhnf(WVar(0, Nil)), TWhnf(WFunction("y" ∷ TWhnf(WVar(1, Nil)), TWhnf(WType(TWhnf(WVar(3, Nil)))))))))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(3)("l")), QPattern(PVar(2)("A")), QPattern(PVar(1)("x")), QPattern(PVar(0)("y"))),
      UTerm(TWhnf(WId(TWhnf(WVar(3, Nil)), TWhnf(WVar(2, Nil)), TWhnf(WVar(1, Nil)), TWhnf(WVar(0, Nil))))),
    )),
    null
  )
}