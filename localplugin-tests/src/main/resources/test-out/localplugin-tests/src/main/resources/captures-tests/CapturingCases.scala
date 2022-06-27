[ERROR] CapturingCases.scala:5: Method/Function in region heap outlives captured symbol [f] living in region stack
    (x: Int) => f(x)
             ^
[ERROR] CapturingCases.scala:8: Method/Function in region heap outlives captured symbol [f] living in region stack
    def inner = f
        ^
[ERROR] CapturingCases.scala:14: Method/Function in region heap outlives captured symbol [f] living in region stack
    def inner(i: I) = f(i)
        ^
[INFO] CapturingCases.scala:1: package <empty>{<empty>.type} {
  import scala.scalanative.annotation.local;
  object CapturingCases extends scala.AnyRef {
    def <init>(): CapturingCases.type = {
      CapturingCases.super.<init>{()Object}(){Object};
      (){Unit}
    }{Unit};
    def capturesLocal1(f: Int => Int @scala.scalanative.annotation.local[Any]): Int => Int = ((x: Int) => f.apply{(v1: Int)Int}(x{Int}){Int}){Int => Int};
    def coerce2FCNested[I, O](f: I => O @scala.scalanative.annotation.local[Any]): I => O @scala.scalanative.annotation.local[Any] = {
      def inner: I => O @scala.scalanative.annotation.local[Any] = f{I => O @scala.scalanative.annotation.local[Any]};
      inner{I => O @scala.scalanative.annotation.local[Any]}
    }{I => O @scala.scalanative.annotation.local[Any]};
    def coerce2FCNested2[I, O](f: I => O @scala.scalanative.annotation.local[Any]): I => O = {
      def inner(i: I): O = f.apply{(v1: I)O}(i{I}){O};
      ((x$1: I) => inner{(i: I)O}(x$1{I}){O}){I => O}
    }{I => O}
  }
}
import scala.scalanative.annotation.local
^
