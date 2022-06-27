import scala.scalanative.annotation.Location.stack

class Filter(sz: Int) {
  sealed trait StackList[@specialized(Int) +A]
  object StackNil extends StackList[Nothing]
  @stack class StackCons[@specialized(Int) +A](val head: A @stack, val tail: StackList[A] @stack) extends StackList[A]

  def unfold(seed: Int): StackList[Int] @stack = {
    if (seed == 0) StackNil
    else new StackCons(seed, unfold(seed - 1))
  }

  val l: StackList[Int] @stack = unfold(sz)
//  def init() = {
//    l = unfold(sz)
//    l
//  }

  def filter(l: StackList[Int] @stack, f: (Int => Boolean)@stack): StackList[Int] @stack = l match {
    case _: StackNil.type => StackNil
    case l: StackCons[Int] => if (f(l.head)) {
      @stack val res = new StackCons[Int](l.head, filter(l.tail, f))
      res
    } else filter(l.tail, f)
  }

  def sum(l: StackList[Int] @stack): Int = l match {
    case _: StackNil.type => 0
    case l: StackCons[Int] => l.head + sum(l.tail)
  }

  def filterSC(rep: Int) = {
    val f = () => Utils.loop(100, _ => {
      sum(filter(l, (v: Int) => (v % 3) == 0))
    })

    Utils.mean_std(rep)(() => f())
  }
}
