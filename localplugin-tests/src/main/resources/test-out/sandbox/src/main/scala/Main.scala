[ERROR] Main.scala:63: Method/Function in region longer.T outlives captured symbol [fooS] living in region shorter.T
    @local[longer.T] val fooL = e => fooS(e)
                                  ^
[INFO] Main.scala:1: package <empty>{<empty>.type} {
  import scala.scalanative.annotation.Location.{somewhere, stack};
  import scala.scalanative.annotation.{Location, Region, local};
  abstract trait Runnable extends scala.AnyRef {
    def init(): Unit;
    def run(): Unit
  };
  object Main extends AnyRef with Flatten {
    def <init>(): Main.type = {
      Main.super.<init>{()Object}(){Object};
      (){Unit}
    }{Unit};
    def returnsLocalInferred[R]: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = {
      @scala.scalanative.annotation.local[R] val res: Int => Int @scala.scalanative.annotation.local[R] = ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[R]};
      @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val xxx: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.-{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
      val tricky: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = if (true{Boolean(true)})
        res{Int => Int @scala.scalanative.annotation.local[R]}
      else
        xxx{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
      @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] val foo: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = ((e: Int) => e.-{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
      val xx: Int => Int @scala.scalanative.annotation.local[Any] = ((e: Int) => e.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[Any]};
      tricky{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
    }{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
    def inc[R](x: Int): Int => Int @scala.scalanative.annotation.local[R] = ((e: Int) => e.+{(x: Int)Int}(x{Int}){Int}){Int => Int @scala.scalanative.annotation.local[R]};
    def firstClass(f: Int => Int): Int = f.apply{(v1: Int)Int}(11{Int(11)}){Int};
    def flatten(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }])(t: Tree @scala.scalanative.annotation.local[r.T]): List[Int] => List[Int] @scala.scalanative.annotation.local[r.T] = t{Tree @scala.scalanative.annotation.local[r.T]} match {
      case (v: Int)Leaf((v @ _{Int}){Int}){Leaf} => ((l: List[Int]) => {
        <synthetic> <artifact> val x$1: Int = v{Int};
        l.::{[B >: Int](x: B)List[B]}[Int]{(x: Int)List[Int]}(x$1{Int}){List[Int]}
      }{List[Int]}){List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]}
      case (l: Tree, r: Tree)Node((t1 @ _{Tree}){Tree}, (t2 @ _{Tree}){Tree}){Node} => ((ll: List[Int]) => {
        val reg: scala.scalanative.annotation.Region{type T >: r.T} @scala.scalanative.annotation.local[T forSome { type T }] = scala.scalanative.annotation.Region.apply{(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }])scala.scalanative.annotation.Region{type T >: r.T} @scala.scalanative.annotation.local[T forSome { type T }]}(r{scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }]}){scala.scalanative.annotation.Region{type T >: r.T} @scala.scalanative.annotation.local[T forSome { type T }]};
        val rec1: List[Int] => List[Int] @scala.scalanative.annotation.local[reg.T] = Main.this.flatten{(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }])(t: Tree @scala.scalanative.annotation.local[r.T])List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]}(reg{scala.scalanative.annotation.Region{type T >: r.T} @scala.scalanative.annotation.local[T forSome { type T }]}){(t: Tree @scala.scalanative.annotation.local[reg.T])List[Int] => List[Int] @scala.scalanative.annotation.local[reg.T]}(t1{Tree}){List[Int] => List[Int] @scala.scalanative.annotation.local[reg.T]};
        val rec2: List[Int] => List[Int] @scala.scalanative.annotation.local[reg.T] = Main.this.flatten{(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }])(t: Tree @scala.scalanative.annotation.local[r.T])List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]}(reg{scala.scalanative.annotation.Region{type T >: r.T} @scala.scalanative.annotation.local[T forSome { type T }]}){(t: Tree @scala.scalanative.annotation.local[reg.T])List[Int] => List[Int] @scala.scalanative.annotation.local[reg.T]}(t2{Tree}){List[Int] => List[Int] @scala.scalanative.annotation.local[reg.T]};
        rec1.apply{(v1: List[Int])List[Int]}(rec2.apply{(v1: List[Int])List[Int]}(ll{List[Int]}){List[Int]}){List[Int]}
      }{List[Int]}){List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]}
    }{List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]};
    def allowRegionInClosure(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }]): Int => Int @scala.scalanative.annotation.local[r.T] = ((i: Int) => {
      val r2: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }] = r{scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }]};
      i{Int}
    }{Int}){Int => Int @scala.scalanative.annotation.local[r.T]};
    def subRegions(): Unit = {
      enter_1stclass{()Unit}(){Unit};
      <synthetic> val res1: Unit = {
        val longer: scala.scalanative.annotation.Region = scala.scalanative.annotation.Region.fresh{scala.scalanative.annotation.Region};
        val shorter: scala.scalanative.annotation.Region{type T >: longer.T} @scala.scalanative.annotation.local[T forSome { type T }] = scala.scalanative.annotation.Region.apply{(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }])scala.scalanative.annotation.Region{type T >: r.T} @scala.scalanative.annotation.local[T forSome { type T }]}(longer{scala.scalanative.annotation.Region}){scala.scalanative.annotation.Region{type T >: longer.T} @scala.scalanative.annotation.local[T forSome { type T }]};
        @scala.scalanative.annotation.local[longer.T] val foo: Int => Int @scala.scalanative.annotation.local[longer.T] = ((i: Int) => i.+{(x: Int)Int}(1{Int(1)}){Int}){Int => Int @scala.scalanative.annotation.local[longer.T]};
        @scala.scalanative.annotation.local[shorter.T] val fooS: Int => Int @scala.scalanative.annotation.local[shorter.T] = ((e: Int) => foo.apply{(v1: Int)Int}(e{Int}){Int}){Int => Int @scala.scalanative.annotation.local[shorter.T]};
        @scala.scalanative.annotation.local[longer.T] val fooL: Int => Int @scala.scalanative.annotation.local[longer.T] = ((e: Int) => fooS.apply{(v1: Int)Int}(e{Int}){Int}){Int => Int @scala.scalanative.annotation.local[longer.T]};
        (){Unit}
      }{Unit};
      exit_1stclass{()Unit}(){Unit};
      res1{Unit}
    }{Unit};
    def escapeRegion(): Int => Int @scala.scalanative.annotation.local[reg.T] forSome { val reg: scala.scalanative.annotation.Region } = {
      val reg: scala.scalanative.annotation.Region = scala.scalanative.annotation.Region.fresh{scala.scalanative.annotation.Region};
      @scala.scalanative.annotation.local[reg.T] val inc: Int => Int @scala.scalanative.annotation.local[reg.T] = ((i: Int) => i{Int}){Int => Int @scala.scalanative.annotation.local[reg.T]};
      inc{Int => Int @scala.scalanative.annotation.local[reg.T]}
    }{Int => Int @scala.scalanative.annotation.local[reg.T]};
    def main(args: Array[String]): Unit = {
      enter_1stclass{()Unit}(){Unit};
      <synthetic> val res2: Unit = {
        val foo: Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = Main.this.returnsLocalInferred{[R]=> Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}[Any]{Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
        Main.this.init{()Unit}(){Unit};
        Main.this.run{()Unit}(){Unit};
        val r: scala.scalanative.annotation.Region = scala.scalanative.annotation.Region.fresh{scala.scalanative.annotation.Region};
        val tmp: List[Int] => List[Int] @scala.scalanative.annotation.local[r.T] = Main.this.flatten{(r: scala.scalanative.annotation.Region @scala.scalanative.annotation.local[T forSome { type T }])(t: Tree @scala.scalanative.annotation.local[r.T])List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]}(r{scala.scalanative.annotation.Region}){(t: Tree @scala.scalanative.annotation.local[r.T])List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]}(Leaf.apply{(v: Int)Leaf}(10{Int(10)}){Leaf}){List[Int] => List[Int] @scala.scalanative.annotation.local[r.T]};
        val res: Int => Int @scala.scalanative.annotation.local[Any] = Main.this.inc{[R](x: Int)Int => Int @scala.scalanative.annotation.local[R]}[Any]{(x: Int)Int => Int @scala.scalanative.annotation.local[Any]}(10{Int(10)}){Int => Int @scala.scalanative.annotation.local[Any]};
        (){Unit}
      }{Unit};
      exit_1stclass{()Unit}(){Unit};
      res2{Unit}
    }{Unit}
  }
}
import scala.scalanative.annotation.Location.{somewhere, stack}
^
