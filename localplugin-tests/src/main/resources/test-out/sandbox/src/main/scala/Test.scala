[INFO] Test.scala:1: package <empty>{<empty>.type} {
  import scala.scalanative.annotation.Location.stack;
  object Test extends scala.AnyRef {
    def <init>(): Test.type = {
      Test.super.<init>{()Object}(){Object};
      (){Unit}
    }{Unit};
    def returnsLocalInferred: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = {
      @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val res: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
      res{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
    }{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
    def returnsLocal: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
    def returnsLocalDeep: Int => (Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]) = ((i: Int) => ((e: Int) => e.+{(x: Int)Int}(i{Int}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}){Int => (Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack])};
    def returnFCasSC(): Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = {
      val inc: Int => Int = ((i: Int) => i.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int};
      inc{Int => Int}
    }{Int => Int};
    def nestedMethods[I, O](f: I => O @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]): (I, Int) => O @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = {
      @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] def inner(e: I, i: Int): O = if (i.>{(x: Int)Boolean}(0{Int(0)}){Boolean})
        inner{(e: I, i: Int)O}(e{I}, i.-{(x: Int)Int}(1{Int(1)}){Int}){O}
      else
        f.apply{(v1: I)O}(e{I}){O}{O};
      {
        ((e: I, i: Int) => inner{(e: I, i: Int)O}(e{I}, i{Int}){O}){(I, Int) => O @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
      }{(I, Int) => O @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
    }{(I, Int) => O @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
    def run(): Unit = {
      enter_1stclass{()Unit}(){Unit};
      <synthetic> val res1: Unit = {
        @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val foo: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        val localPropagatedInApply: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = Test.this.returnsLocalDeep.apply{(v1: Int)Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}(10{Int(10)}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        val cannotCoerceLocal: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = {
          scala.Predef.println{(x: Any)Unit}("HEY"{String("HEY")}){Unit};
          @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val tmp: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((i: Int) => i.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
          tmp{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
        }{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        val xx: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = if (false{Boolean(false)})
          ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int}
        else
          {
            @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val res: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.-{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
            res{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
          }{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        val ifCase: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = if (true{Boolean(true)})
          {
            @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val tmp: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
            tmp{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
          }{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
        else
          ((e: Int) => e.-{(x: Int)Int}(1{Int(1)}){Int}){Int => Int}{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        val matchCase: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = true{Boolean(true)} match {
          case true{Boolean(true)} => cannotCoerceLocal{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
          case false{Boolean(false)} => xx{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
        }{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        (){Unit}
      }{Unit};
      exit_1stclass{()Unit}(){Unit};
      res1{Unit}
    }{Unit}
  }
}
import scala.scalanative.annotation.Location.stack
^
