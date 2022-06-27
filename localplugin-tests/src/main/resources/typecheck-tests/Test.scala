import scala.scalanative.annotation.Location.stack

object FailTypeCheck {
  def coerce2FC[I, O](f: (I => O)@stack): (I => O) = f

  def foo[I](f: I => Unit): Unit = ???

  def app = {
    @stack val pp = (s: String) => println(s)
    foo(pp)
  }

  def coerceFCDeep(f: Int => (Int => Int)@stack): Int => Int => Int = f
}
