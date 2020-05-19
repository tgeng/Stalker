package io.github.tgeng.stalker.core.tt

import io.github.tgeng.stalker.common.QualifiedName._

import DeclarationT._
import Term._
import Whnf._
import Level._
import ClauseT._
import Pattern._
import CoPattern._
import CaseTree._
import UncheckedRhs._

object builtins {
  private val parent = Root / "stalker" / "builtins"

  val levelType: PreDeclaration = DefinitionT(parent / "Level")(
    TWhnf(WUniverse(lconst(0))),
    Seq(UncheckedClause(
      Nil,
      UTerm(TWhnf(WLevelType)),
    )), 
    null
  )

  val universeType: PreDeclaration = DefinitionT(parent / "Type")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevelType), TWhnf(WUniverse(lsuc(lvar(0)))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(0)("l"))),
      UTerm(TWhnf(WUniverse(lvar(0)))),
    )),
    null
  )
  
  val lsucFn: PreDeclaration = DefinitionT(parent / "lsuc")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevelType), TWhnf(WLevelType))),
    Seq(UncheckedClause(
      List(QPattern(PVar(0)("l"))),
      UTerm(TWhnf(WLevel(lsuc(lvar(0))))),
    )),
    null
  )

  val lmaxFn: PreDeclaration = DefinitionT(parent / "lmax")(
    TWhnf(WFunction("l1" ∷ TWhnf(WLevelType), TWhnf(WFunction("l2" ∷ TWhnf(WLevelType), TWhnf(WLevelType))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(1)("l1")), QPattern(PVar(0)("l2"))),
      UTerm(TWhnf(WLevel(lmax(lvar(1), lvar(0))))),
    )),
    null
  )

  val idType: PreDeclaration = DefinitionT(parent / "Id")(
    TWhnf(WFunction("l" ∷ TWhnf(WLevelType), TWhnf(WFunction("A" ∷ TWhnf(WUniverse(lvar(0))), TWhnf(WFunction("x" ∷ TWhnf(WVar(0, Nil)), TWhnf(WFunction("y" ∷ TWhnf(WVar(1, Nil)), TWhnf(WUniverse(lvar(3))))))))))),
    Seq(UncheckedClause(
      List(QPattern(PVar(3)("l")), QPattern(PVar(2)("A")), QPattern(PVar(1)("x")), QPattern(PVar(0)("y"))),
      UTerm(TWhnf(WId(lvar(3), TWhnf(WVar(2, Nil)), TWhnf(WVar(1, Nil)), TWhnf(WVar(2, Nil))))),
    )),
    null
  )
}