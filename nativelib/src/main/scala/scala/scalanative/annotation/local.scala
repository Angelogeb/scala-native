package scala.scalanative.annotation

final class local[-T] extends scala.annotation.StaticAnnotation with scala.annotation.TypeConstraint

object Location {
  type Stack = Any
  type Heap = Nothing

  type stack = local[Stack]
  type heap = local[Heap]
}
