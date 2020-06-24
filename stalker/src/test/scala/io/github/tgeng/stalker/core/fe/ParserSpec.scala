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
      List(FQPattern(FPForced(FTRedux(List("a"),List())))))
    assert(q"a b ..c" ==
      List(FQPattern(FPVarCon("a")), FQPattern(FPVarCon("b")), FQPattern(FPForced(FTRedux(List("c"),List())))))
    assert(q"..(a b c)" ==
      List(FQPattern(FPForced(FTRedux(List("a"),List(FETerm(FTRedux(List("b"),List())), FETerm(FTRedux(List("c"),List()))))))))
    assert(q"a ..(b c) .d" ==
      List(FQPattern(FPVarCon("a")), FQPattern(FPForced(FTRedux(List("b"),List(FETerm(FTRedux(List("c"),List())))))), FQProj("d")))
    assert(q"(..a b c) " ==
      List(FQPattern(FPCon(List("a"), List(FPVarCon("b"), FPVarCon("c")), true))))

    assert(q"a{}" == List(FQPattern(FPCon("a", List(), false))))
    assert(q"a{b c}" == List(FQPattern(FPCon("a", List(FPVarCon("b"), FPVarCon("c")), false))))
    assert(q"a{..b c}" == List(FQPattern(FPCon("a", List(FPForced(FTRedux(List("b"),List())), FPVarCon("c")), false))))
    assert(q"..a{b c}" == List(FQPattern(FPCon("a", List(FPVarCon("b"), FPVarCon("c")), true))))
    assert(q"x ..a{b c} y" == List(FQPattern(FPVarCon("x")), FQPattern(FPCon("a", List(FPVarCon("b"), FPVarCon("c")), true)), FQPattern(FPVarCon("y"))))
    assert(q"a{b{} c}" == List(FQPattern(FPCon("a", List(FPCon("b", List(), false), FPVarCon("c")), false))))
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
            FConstructor("Zero",List()),
            FConstructor("Suc",List(FBinding("",FTRedux(List("Nat"),List()))))))
    )

    assert(
      decl"""
      |data Vector (n : Nat)(A : Type 0lv) : Type 0lv where
      |  Nil : Id 0lv Nat n Zero -> Vector n A
      |  Cons : (m : Nat) -> A -> Vector m A -> Id 0lv Nat (Suc m) n -> Vector n A
      """ ==
        FData(
          "Vector",
          List(FBinding("n", FTRedux(List("Nat"), List())), FBinding("A", FTRedux(List("Type"), List(FETerm(FTLevel(0)))))),
          FTRedux(List("Type"), List(FETerm(FTLevel(0)))),
          Vector(
            FConstructor(
              "Nil", 
              List(
                FBinding("", FTRedux(List("Id"), List(FETerm(FTLevel(0)), FETerm(FTRedux(List("Nat"), List())), FETerm(FTRedux(List("n"), List())), FETerm(FTRedux(List("Zero"), List()))))))),
            FConstructor(
              "Cons",
              List(
                FBinding("m", FTRedux(List("Nat"), List())),
                FBinding("", FTRedux(List("A"), List())),
                FBinding("", FTRedux(List("Vector"), List(FETerm(FTRedux(List("m"), List())), FETerm(FTRedux(List("A"), List()))))),
                FBinding("", FTRedux(List("Id"), List(FETerm(FTLevel(0)), FETerm(FTRedux(List("Nat"), List())), FETerm(FTRedux(List("Suc"), List(FETerm(FTRedux(List("m"), List()))))), FETerm(FTRedux(List("n"), List())))))))))
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
      |  = Nat.Suc Nat.Zero
      """ == FDefinition(
        "one", 
        FTRedux(List("Nat"), List()), 
        Vector(
          FUncheckedClause(
            List(),
            FUTerm(FTRedux(List("Nat", "Suc"), List(FETerm(FTRedux(List("Nat", "Zero"), List()))))))))
    )

    assert(
      decl"""
      |def suc : Nat -> Nat
      |  n = Nat.Suc n
      """ == FDefinition(
        "suc", 
        FTFunction(FBinding("", FTRedux(List("Nat"), List())), FTRedux(List("Nat"), List())),
        Vector(
          FUncheckedClause(
            List(FQPattern(FPVarCon("n"))),
            FUTerm(FTRedux(List("Nat", "Suc"), List(FETerm(FTRedux(List("n"), List()))))))))
    )

    assert(
      decl"""
      |def plus : Nat -> Nat -> Nat
      |  m Nat.Zero = m
      |  m (Nat.Suc n) = Nat.Suc (plus m n)
      """ == FDefinition(
        "plus", 
        FTFunction(FBinding("", FTRedux(List("Nat"), List())), FTFunction(FBinding("", FTRedux(List("Nat"), List())), FTRedux(List("Nat"), List()))),
        Vector(
          FUncheckedClause(
            List(FQPattern(FPVarCon("m")), FQPattern(FPCon(List("Nat", "Zero"), List(), false))),
            FUTerm(FTRedux(List("m"), List()))),
          FUncheckedClause(
            List(FQPattern(FPVarCon("m")), FQPattern(FPCon(List("Nat", "Suc"), List(FPVarCon("n")), false))),
            FUTerm(FTRedux(List("Nat", "Suc"), List(FETerm(FTRedux(List("plus"), List(FETerm(FTRedux(List("m"), List())), FETerm(FTRedux(List("n"), List())))))))))))
    )
  }
}