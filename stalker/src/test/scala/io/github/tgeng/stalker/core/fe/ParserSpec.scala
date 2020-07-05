package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import io.github.tgeng.parse._
import io.github.tgeng.stalker.core.fe.parser._
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}
import io.github.tgeng.testing.UnitSpec
import io.github.tgeng.parse.string.toStringWithInput

class ParserSpec extends UnitSpec {

  "Parsing Term round trips" in {
    roundTrip(
      "A",
      "fn a b c",
      "0lv",
      "a (b c)",
      "A -> B -> C",
      "(A -> B) -> C",
      "(n : Nat) -> (A : Type) -> Vector n A",
      """
      |(vecFn : (n : Nat) -> (A : Type) -> Vector n A) ->
      |(m : Nat) ->
      |(n : Nat) ->
      |Vector n (Vector m String)
      """,
      """
      |(veryLongFn : (a : A) ->
      |              (b : B) ->
      |              (c : A -> B -> C) ->
      |              (d : A -> B -> D) ->
      |              Type) ->
      |(a : A) ->
      |(b : B) ->
      |(c : A -> B -> C) ->
      |(d : A -> B -> D) ->
      |veryLongFn a b c d
      """,
      "con1{a, b, c}",
      """
      |con1{
      |  (a b c d e)
      |  (A -> B -> C -> D -> E)
      |  con2{(a b c d e) (A -> B -> C -> D -> E) (x y z)}
      |  con3{(x y z)}
      |}
      """,
      "(a : Nat) -> (f : Nat -> Nat) -> (g : Nat -> Nat -> Nat) -> f (f (f a))",
      "(a : Nat) -> (f : Nat -> Nat) -> (g : Nat -> Nat -> Nat) -> g (f a) (f a)",
      "(a : Nat) -> (f : Nat -> Nat) -> (g : Nat -> Nat -> Nat) -> f (g (f a) (f a))",
    )
  }

  private def roundTrip(inputs: String*) = for (input <- inputs) {
    val stripped = input.stripMargin.trim.asInstanceOf[String]
    (term << eof).parse(stripped) match {
      case Left(e) => fail(s"When parsing:\n$stripped\nit failed with error:\n${e.toStringWithInput(input)}")
      case Right(t) => {
        assert(t.toBlock.toString == stripped)
      }
    }
  }

  import io.github.tgeng.stalker.core.fe.builders._

  import FPattern._
  import FCoPattern._
  import FElimination._
  import FTerm._
  import FDeclaration._
  import FUncheckedRhs._

  "Parsing Pattern" in {
    assert(q"a b c" == List(FQPattern(FPVar("a")), FQPattern(FPVar("b")), FQPattern(FPVar("c"))))
    assert(q"a .b .c d" == List(FQPattern(FPVar("a")), FQProj("b"), FQProj("c"), FQPattern(FPVar("d"))))

    assert(q"..a" ==
      List(FQPattern(FPForced(FTRedux(List("a"),List())))))
    assert(q"a b ..c" ==
      List(FQPattern(FPVar("a")), FQPattern(FPVar("b")), FQPattern(FPForced(FTRedux(List("c"),List())))))
    assert(q"..(a b c)" ==
      List(FQPattern(FPForced(FTRedux(List("a"),List(FETerm(FTRedux(List("b"),List())), FETerm(FTRedux(List("c"),List()))))))))
    assert(q"a ..(b c) .d" ==
      List(FQPattern(FPVar("a")), FQPattern(FPForced(FTRedux(List("b"),List(FETerm(FTRedux(List("c"),List())))))), FQProj("d")))
    assert(q"..a{} b c" ==
      List(FQPattern(FPCon("a", List(), true)), FQPattern(FPVar("b")), FQPattern(FPVar("c"))))

    assert(q"a{}" == List(FQPattern(FPCon("a", List(), false))))
    assert(q"a{b c}" == List(FQPattern(FPCon("a", List(FPVar("b"), FPVar("c")), false))))
    assert(q"a{..b c}" == List(FQPattern(FPCon("a", List(FPForced(FTRedux(List("b"),List())), FPVar("c")), false))))
    assert(q"..a{b c}" == List(FQPattern(FPCon("a", List(FPVar("b"), FPVar("c")), true))))
    assert(q"x ..a{b c} y" == List(FQPattern(FPVar("x")), FQPattern(FPCon("a", List(FPVar("b"), FPVar("c")), true)), FQPattern(FPVar("y"))))
    assert(q"a{b{} c}" == List(FQPattern(FPCon("a", List(FPCon("b", List(), false), FPVar("c")), false))))
  }

  "data declaration" in {
    assert(
      decl"""
      |data Nat : Type 0lv where
      |  Zero : Nat
      |  Suc : Nat -> Nat
      """ ==
        FData(
          "Nat",
          List(),
          FTRedux(List("Type"),List(FETerm(FTLevel(0)))),
          Vector(
            FConstructor("Zero",List(), Nil),
            FConstructor("Suc",List(FBinding("",FTRedux(List("Nat"),List()))), Nil)))
    )

    assert(
      decl"""
      |data Vector (n : Nat)(A : Type 0lv) : Type 0lv where
      |  Nil : Vector Zero{} A
      |  Cons : (m : Nat) -> A -> Vector m A -> Vector Suc{m} A
      """ ==
        FData(
          "Vector",
          List(FBinding("n", FTRedux(List("Nat"), List())), FBinding("A", FTRedux(List("Type"), List(FETerm(FTLevel(0)))))),
          FTRedux(List("Type"), List(FETerm(FTLevel(0)))),
          Vector(
            FConstructor("Nil", List(), List(FTCon("Zero", List()), FTRedux(List("A"), List()))),
            FConstructor(
              "Cons",
              List(
                FBinding("m", FTRedux(List("Nat"), List())),
                FBinding("", FTRedux(List("A"), List())),
                FBinding("", FTRedux(List("Vector"), List(FETerm(FTRedux(List("m"), List())), FETerm(FTRedux(List("A"), List())))))),
              List(FTCon("Suc", List(FTRedux(List("m"), List()))), FTRedux(List("A"), List())))))
    )
  }

  "record declaration" in {
    assert(
      decl"""
      |record NatStream : Type 0lv where
      |  head : Nat
      |  tail : NatStream
      """ == FRecord(
        "NatStream",
        List(),
        FTRedux(List("Type"), List(FETerm(FTLevel(0)))),
        Vector(
          FField("head", FTRedux(List("Nat"), List())),
          FField("tail", FTRedux(List("NatStream"), List()))))
    )

    assert(
      decl"""
      |record CoNat : Type 0lv where
      |  izZero : Boolean
      |  tail : Id 0lv Boolean (self .izZero) true -> CoNat
      """ == FRecord(
        "CoNat",
        List(),
        FTRedux(List("Type"), List(FETerm(FTLevel(0)))),
        Vector(
          FField("izZero", FTRedux(List("Boolean"), List())),
          FField(
            "tail",
            FTFunction(
              FBinding(
                "", 
                FTRedux(List("Id"), List(FETerm(FTLevel(0)), FETerm(FTRedux(List("Boolean"), List())), FETerm(FTRedux(List("self"), List(FEProj("izZero")))), FETerm(FTRedux(List("true"), List()))))),
              FTRedux(List("CoNat"), List())))))
    )

    assert(
      decl"""
      |def one : Nat
      |  = Suc{Zero{}}
      """ == FDefinition("one", FTRedux(List("Nat"), List()), Vector(FUncheckedClause(List(),FUTerm(FTCon("Suc", List(FTCon("Zero", List())))))))
    )

    assert(
      decl"""
      |def suc : Nat -> Nat
      |  n = Suc{n}
      """ == FDefinition(
        "suc",
        FTFunction(FBinding("", FTRedux(List("Nat"), List())), FTRedux(List("Nat"), List())),
        Vector(FUncheckedClause(List(FQPattern(FPVar("n"))),FUTerm(FTCon("Suc", List(FTRedux(List("n"), List())))))))
    )

    assert(
      decl"""
      |def plus : Nat -> Nat -> Nat
      |  m Zero{} = m
      |  m Suc{n} = Suc{plus m n}
      """ == FDefinition(
        "plus",
        FTFunction(FBinding("", FTRedux(List("Nat"), List())), FTFunction(FBinding("", FTRedux(List("Nat"), List())), FTRedux(List("Nat"), List()))),
        Vector(FUncheckedClause(List(FQPattern(FPVar("m")), FQPattern(FPCon("Zero", List(), false))),FUTerm(FTRedux(List("m"), List()))), FUncheckedClause(List(FQPattern(FPVar("m")), FQPattern(FPCon("Suc", List(FPVar("n")), false))),FUTerm(FTCon("Suc", List(FTRedux(List("plus"), List()), FTRedux(List("m"), List()), FTRedux(List("n"), List())))))))
    )

    import ModuleCommand._
    import Visibility._

    assert(cmd"import a as b" == Seq(MNsOp(List("a"), List("b"), Private)))
    assert(cmd"import a.b.c as b.c.d" == Seq(MNsOp(List("a", "b", "c"), List("b", "c", "d"), Private)))
    assert(cmd"import stalker.data.Nat" == Seq(MNsOp(List("stalker", "data", "Nat"), List("Nat"), Private)))
    assert(cmd"import stalker.data._" == Seq(MNsOp(List("stalker", "data"), List(), Private)))
    assert(cmd"public import stalker.data.Nat" == Seq(MNsOp(List("stalker", "data", "Nat"), List("Nat"), Private), MNsOp(List("stalker", "data", "Nat"), List("Nat"), Internal), MNsOp(List("stalker", "data", "Nat"), List("Nat"), Public)))
    assert(cmd"public import stalker.data._" == Seq(MNsOp(List("stalker", "data"), List(), Private), MNsOp(List("stalker", "data"), List(), Internal), MNsOp(List("stalker", "data"), List(), Public)))

    assert(cmd"export a as b" == Seq(MNsOp(List("a"), List("b"), Internal), MNsOp(List("a"), List("b"), Public)))
    assert(cmd"internal export a.b.c as b.c.d" == Seq(MNsOp(List("a", "b", "c"), List("b", "c", "d"), Internal)))
    assert(cmd"internal export stalker.data.Nat" == Seq(MNsOp(List("stalker", "data", "Nat"), List("Nat"), Internal)))
    assert(cmd"internal export stalker.data._" == Seq(MNsOp(List("stalker", "data"), List(), Internal)))

    assert(cmd"""
    |data Nat : Type 0lv where
    |  Zero : Nat
    |  Suc : Nat -> Nat
    """ ==
      Seq(MDecl(
        FData(
          "Nat",
          List(),
          FTRedux(List("Type"),List(FETerm(FTLevel(0)))),
          Vector(
            FConstructor("Zero",List(), Nil),
            FConstructor("Suc",List(FBinding("",FTRedux(List("Nat"),List()))), Nil))), Visibility.Public)))

    assert(cmd"private data Nat : Type 0lv where" == 
      Seq(MDecl(FData("Nat", List(), FTRedux(List("Type"),List(FETerm(FTLevel(0)))), Vector()), Visibility.Private)))
    assert(cmd"internal data Nat : Type 0lv where" == 
      Seq(MDecl(FData("Nat", List(), FTRedux(List("Type"),List(FETerm(FTLevel(0)))), Vector()), Visibility.Internal)))
  }
}