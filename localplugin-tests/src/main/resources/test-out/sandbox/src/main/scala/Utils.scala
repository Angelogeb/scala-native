[INFO] Utils.scala:1: package <empty>{<empty>.type} {
  import scala.scalanative.annotation.local;
  object Utils extends scala.AnyRef {
    def <init>(): Utils.type = {
      Utils.super.<init>{()Object}(){Object};
      (){Unit}
    }{Unit};
    def time(f: => Any): (Any, Long) = {
      val start: Long = java.lang.System.nanoTime{()Long}(){Long};
      val res: Any = f{Any};
      val time: Long = java.lang.System.nanoTime().-(start)./{(x: Int)Long}(1000000{Int(1000000)}){Long};
      scala.Tuple2.apply{[T1, T2](_1: T1, _2: T2)(T1, T2)}[Any, Long]{(_1: Any, _2: Long)(Any, Long)}(res{Any}, time{Long}){(Any, Long)}
    }{(Any, Long)};
    def repeated(n: Int)(f: => Any): Unit = {
      var i: Int = 0{Int(0)};
      while$1(){
        if (i.<{(x: Int)Boolean}(n{Int}){Boolean})
          {
            {
              val res: Any = f{Any};
              i{Int} = i.+{(x: Int)Int}(1{Int(1)}){Int}{Unit}
            }{Unit};
            while$1{()Unit}(){Unit}
          }{Unit}
        else
          (){Unit}{Unit}
      }{Unit}
    }{Unit}
  }
}
import scala.scalanative.annotation.local
^
