import scala.scalanative.annotation.local

object CapturingCases {
  def capturesLocal1(f: (Int => Int)@local): Int => Int =
    (x: Int) => f(x)

  def coerce2FCNested[I, O](f: (I => O)@local) = {
    def inner = f

    inner
  }

  def coerce2FCNested2[I, O](f: (I => O)@local) = {
    def inner(i: I) = f(i)

    inner(_)
  }
}
