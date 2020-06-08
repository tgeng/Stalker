package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import io.github.tgeng.parse._
import io.github.tgeng.stalker.core.fe.parser._
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}
import io.github.tgeng.stalker.testing.UnitSpec
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

  "Parsing Pattern" in {
    assert(q"a b c" == List(FQPattern(FPVarCon("a")), FQPattern(FPVarCon("b")), FQPattern(FPVarCon("c"))))
    assert(q"a .b .c d" == List(FQPattern(FPVarCon("a")), FQProj("b"), FQProj("c"), FQPattern(FPVarCon("d"))))
    assert(q"(con a b)" == List(FQPattern(FPCon(List("con"), List(FPVarCon("a"), FPVarCon("b")), false))))
    assert(q"(con a b) .foobar" == List(FQPattern(FPCon(List("con"), List(FPVarCon("a"), FPVarCon("b")), false)), FQProj("foobar")))
    assert(q"(con a b) (con c d)" ==
      List(FQPattern(FPCon(List("con"), List(FPVarCon("a"), FPVarCon("b")), false)), FQPattern(FPCon(List("con"), List(FPVarCon("c"), FPVarCon("d")), false))))
    assert(q"foo.bar" ==
      List(FQPattern(FPCon(List("foo", "bar"), List(), false))))
    assert(q"foo.bar a b" ==
      List(FQPattern(FPCon(List("foo", "bar"), List(), false)), FQPattern(FPVarCon("a")), FQPattern(FPVarCon("b"))))
    assert(q"(foo.bar a b)" ==
      List(FQPattern(FPCon(List("foo", "bar"), List(FPVarCon("a"), FPVarCon("b")), false))))

    assert(q"..a" ==
      List(FQPattern(FPForced(FTRedux("a",List(),List())))))
    assert(q"a b ..c" ==
      List(FQPattern(FPVarCon("a")), FQPattern(FPVarCon("b")), FQPattern(FPForced(FTRedux("c",List(),List())))))
    assert(q"..(a b c)" ==
      List(FQPattern(FPForced(FTRedux("a",List(),List(FETerm(FTRedux("b",List(),List())), FETerm(FTRedux("c",List(),List()))))))))
    assert(q"a ..(b c) .d" ==
      List(FQPattern(FPVarCon("a")), FQPattern(FPForced(FTRedux("b",List(),List(FETerm(FTRedux("c",List(),List())))))), FQProj("d")))
    assert(q"(..a b c) " ==
      List(FQPattern(FPCon(List("a"), List(FPVarCon("b"), FPVarCon("c")), true))))

    assert(q"a{}" == List(FQPattern(FPCon("a", List(), false))))
    assert(q"a{b c}" == List(FQPattern(FPCon("a", List(FPVarCon("b"), FPVarCon("c")), false))))
    assert(q"a{..b c}" == List(FQPattern(FPCon("a", List(FPForced(FTRedux("b",List(),List())), FPVarCon("c")), false))))
    assert(q"..a{b c}" == List(FQPattern(FPCon("a", List(FPVarCon("b"), FPVarCon("c")), true))))
    assert(q"x ..a{b c} y" == List(FQPattern(FPVarCon("x")), FQPattern(FPCon("a", List(FPVarCon("b"), FPVarCon("c")), true)), FQPattern(FPVarCon("y"))))
    assert(q"a{b{} c}" == List(FQPattern(FPCon("a", List(FPCon("b", List(), false), FPVarCon("c")), false))))
  }

  import FDeclaration._

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
          FTRedux("Type",List(),List(FETerm(FTLevel(0)))),
          Vector(
            FConstructor("Zero",List()),
            FConstructor("Suc",List(FBinding("",FTRedux("Nat",List(),List()))))))
    )

    assert(
      decl"""
      |data Nat : Type 0lv
      """ == FData("Nat", List(), FTRedux("Type", List(), List(FETerm(FTLevel(0)))), null)
    )

    assert(
      decl"""
      |data Nat where
      |  Zero : Nat
      |  Suc : Nat -> Nat
      """ ==
        FDataDef(
          "Nat",
          Vector(
            FConstructor("Zero", List()),
            FConstructor("Suc", List(FBinding("", FTRedux("Nat", List(), List()))))))
    )

    assert(
      decl"""
      |data Vector (n : Nat)(A : Type 0lv) : Type 0lv where
      |  Nil : (m : Nat) -> Id 0lv m Zero -> Vector n A
      |  Cons : (m : Nat) -> A -> Vector m A -> Id 0lv (Suc m) n -> Vector n A
      """ ==
        FData(
          "Vector",
          List(FBinding("n", FTRedux("Nat", List(), List())), FBinding("A", FTRedux("Type", List(), List(FETerm(FTLevel(0)))))),
          FTRedux("Type", List(), List(FETerm(FTLevel(0)))),
          Vector(
            FConstructor(
              "Nil", 
              List(
                FBinding("m", FTRedux("Nat", List(), List())),
                FBinding("", FTRedux("Id", List(), List(FETerm(FTLevel(0)), FETerm(FTRedux("m", List(), List())), FETerm(FTRedux("Zero", List(), List()))))))),
            FConstructor(
              "Cons",
              List(
                FBinding("m", FTRedux("Nat", List(), List())),
                FBinding("", FTRedux("A", List(), List())),
                FBinding("", FTRedux("Vector", List(), List(FETerm(FTRedux("m", List(), List())), FETerm(FTRedux("A", List(), List()))))),
                FBinding("", FTRedux("Id", List(), List(FETerm(FTLevel(0)), FETerm(FTRedux("Suc", List(), List(FETerm(FTRedux("m", List(), List()))))), FETerm(FTRedux("n", List(), List())))))))))
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
        FTRedux("Type", List(), List(FETerm(FTLevel(0)))),
        Vector(
          FField("head", FTRedux("Nat", List(), List())),
          FField("tail", FTRedux("NatStream", List(), List()))))
    )

    assert(
      decl"""
      |record NatStream : Type 0lv
      """ == FRecord(
        "NatStream",
        List(),
        FTRedux("Type", List(), List(FETerm(FTLevel(0)))),
        null)
    )

    assert(
      decl"""
      |record NatStream where
      |  head : Nat
      |  tail : NatStream
      """ == FRecordDef(
        "NatStream",
        Vector(
          FField("head", FTRedux("Nat", List(), List())),
          FField("tail", FTRedux("NatStream", List(), List()))))
    )

    assert(
      decl"""
      |record CoNat where
      |  izZero : Boolean
      |  tail : Id 0lv Boolean (self .izZero) true -> CoNat
      """ == FRecordDef(
        "CoNat",
        Vector(
          FField("izZero", FTRedux("Boolean", List(), List())),
          FField(
            "tail",
            FTFunction(
              FBinding(
                "", 
                FTRedux("Id", List(), List(FETerm(FTLevel(0)), FETerm(FTRedux("Boolean", List(), List())), FETerm(FTRedux("self", List(), List(FEProj("izZero")))), FETerm(FTRedux("true", List(), List()))))),
              FTRedux("CoNat", List(), List())))))
    )
  }
}