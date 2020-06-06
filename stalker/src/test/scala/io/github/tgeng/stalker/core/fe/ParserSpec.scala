package io.github.tgeng.stalker.core.fe

import scala.language.implicitConversions
import io.github.tgeng.parse._
import io.github.tgeng.stalker.core.fe.parser._
import io.github.tgeng.stalker.core.fe.pprint.{given _, _}
import io.github.tgeng.stalker.testing.UnitSpec

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
      case Left(e) => fail(s"When parsing:\n$stripped\nit failed with error:\n$e")
      case Right(t) => {
        assert(t.toBlock.toString == stripped)
      }
    }
  }

  import io.github.tgeng.stalker.core.fe.builders.q

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
}