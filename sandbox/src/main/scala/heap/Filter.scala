package heap
import scala.scalanative.annotation.Location.stack

class Filter(sz: Int) {
  sealed trait StackList[@specialized(Int) +A]
  object StackNil extends StackList[Nothing]
   class StackCons[@specialized(Int) +A](val head: A , val tail: StackList[A] ) extends StackList[A]

  def unfold(seed: Int): StackList[Int]  = {
    if (seed == 0) StackNil
    else new StackCons(seed, unfold(seed - 1))
  }

  var l: StackList[Int]  = _
  def init() = {
    l = unfold(sz)
    l
  }

  def filter(l: StackList[Int] , f: (Int => Boolean)): StackList[Int]  = l match {
    case _: StackNil.type => StackNil
    case l: StackCons[Int] => if (f(l.head)) {
       val res = new StackCons[Int](l.head, filter(l.tail, f))
      res
    } else filter(l.tail, f)
  }

  def sum(l: StackList[Int] ): Int = l match {
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
