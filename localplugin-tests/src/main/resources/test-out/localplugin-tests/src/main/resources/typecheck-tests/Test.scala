[ERROR] Test.scala:4: type mismatch;
 found   : I => O @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]
    (which expands to)  I => O @scala.scalanative.annotation.local[Any]
 required: I => O

  def coerce2FC[I, O](f: (I => O)@stack): (I => O) = f
                                                     ^
[ERROR] Test.scala:10: type mismatch;
 found   : String => Unit @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]
    (which expands to)  String => Unit @scala.scalanative.annotation.local[Any]
 required: ? => Unit

    foo(pp)
        ^
[ERROR] Test.scala:13: type mismatch;
 found   : Int => (Int => Int @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack])
    (which expands to)  Int => (Int => Int @scala.scalanative.annotation.local[Any])
 required: Int => (Int => Int)
  def coerceFCDeep(f: Int => (Int => Int)@stack): Int => Int => Int = f
                                                                      ^
