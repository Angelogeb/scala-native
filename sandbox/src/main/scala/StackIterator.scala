import scala.collection.mutable.{ArrayBuffer, ListBuffer}
import scala.reflect.ClassTag
import scala.scalanative.annotation.Location.stack

object StackIterator {
  val empty: StackIterator[Nothing] = new StackIterator[Nothing] {
    def hasNext: Boolean = false
    def next(): Nothing = throw new NoSuchElementException("next on empty iteratorr")
  }


  def tabulate[A](end: Int)(f: Int => A): StackIterator[A] = new StackIterator[A] {
    private var i = 0
    def hasNext: Boolean = i < end
    def next(): A =
      if (hasNext) { val result = f(i); i += 1; result }
      else empty.next()
  }

  def range(start: Int, end: Int): StackIterator[Int] = range(start, end, 1)

  def range(start: Int, end: Int, step: Int): StackIterator[Int] = new StackIterator[Int] {
    if (step == 0) throw new IllegalArgumentException("zero step")
    private var i = start
    def hasNext: Boolean = (step <= 0 || i < end) && (step >= 0 || i > end)
    def next(): Int =
      if (hasNext) { val result = i; i += step; result }
      else empty.next()
  }

  def fromIterator[A](i: Iterator[A]) = new StackIterator[A] {
    override def hasNext: Boolean = i.hasNext
    override def next(): A = i.next()
  }

  def fromList[A](l: List[A]) = new StackIterator[A] {
    private var head = l
    override def hasNext: Boolean = !head.isInstanceOf[Nil.type]
    override def next(): A =
      if (hasNext) {
        val res = head.head
        head = head.tail
        res
      } else empty.next()
  }
}

@stack sealed trait StackIterator[+A] { self =>
  def hasNext: Boolean
  def next(): A

  def toArray[B >: A : ClassTag]: Array[B] = {
    val a = ArrayBuffer[B]()
    while (hasNext) {
      a += next
    }
    a.toArray
  }

  def drop(n: Int): StackIterator[A] = {
    var j = 0
    while (j < n && hasNext) {
      next()
      j += 1
    }
    this
  }

  def map[B](f: (A => B) @stack): StackIterator[B] = new StackIterator[B] {
    def hasNext = self.hasNext
    @stack def next() = f(self.next())
  }

  def filter(p: (A => Boolean) @stack): StackIterator[A] = new StackIterator[A] {
    private var hd: A = _
    private var hdDefined: Boolean = false

    @stack def hasNext: Boolean = hdDefined || {
      do {
        if (!self.hasNext) return false
        hd = self.next()
      } while (!p(hd))
      hdDefined = true
      true
    }
    def next() = if (hasNext) { hdDefined = false; hd } else StackIterator.empty.next()
  }

  def foldLeft[B](z: B)(f: ((B, A) => B) @stack): B = {
    var res = z
    while (hasNext) {
      res = f(res, next)
    }
    res
  }

  def collect[B](pf: PartialFunction[A, B]): StackIterator[B] = new StackIterator[B] {
    // Manually buffer to avoid extra layer of wrapping with buffered
    private[this] var hd: A = _

    // Little state machine to keep track of where we are
    // Seek = 0; Found = 1; Empty = -1
    // Not in vals because scalac won't make them static (@inline def only works with -optimize)
    // BE REALLY CAREFUL TO KEEP COMMENTS AND NUMBERS IN SYNC!
    private[this] var status = 0/*Seek*/

    def hasNext = {
      while (status == 0/*Seek*/) {
        if (self.hasNext) {
          hd = self.next()
          if (pf.isDefinedAt(hd)) status = 1/*Found*/
        }
        else status = -1/*Empty*/
      }
      status == 1/*Found*/
    }
    def next() = if (hasNext) { status = 0/*Seek*/; pf(hd) } else StackIterator.empty.next()
  }

  def zip[B](that: StackIterator[B]): StackIterator[(A, B)] = new StackIterator[(A, B)] {
    def hasNext = self.hasNext && that.hasNext
    def next = (self.next(), that.next())
  }

  def copyToArray[B >: A](xs: Array[B], start: Int, len: Int): Int = {
    var i = start
    val end = start + math.min(len, xs.length - start)
    while (i < end && hasNext) {
      xs(i) = next()
      i += 1
    }
    i - start
  }
}
