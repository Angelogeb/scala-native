import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.scalanative.runtime.Local
import scala.util.Random

class IteratorExamples(nEvents: Int, maxNodes: Int = 10, insertionProb: Double = 0.5) {

  val seed = 42

  def updatingGraph2() = {
    Random.setSeed(seed)
    val adjList = mutable.Map[Int, ListBuffer[(Int, Int)]]()
    val a = StackIterator
      .range(0, nEvents)
      .map[Int](_ => {
        val source = Random.nextInt(maxNodes)
        val kind = Random.nextDouble()
        val l = adjList.getOrElseUpdate(source, ListBuffer.empty)
        if (kind < insertionProb) { // Insert
          val dest = Random.nextInt(maxNodes)
          val value = Random.nextInt(100)
          l.append((dest, value))
        } else {
          val len = l.length
          if (len > 0) {
            val idx = Random.nextInt(len)
            l.remove(idx)
          }
        }

        val res = StackIterator
          .fromIterator(l.iterator)
          .map[Int](dest_v1 => {

            StackIterator
              .fromIterator(l.iterator)
              .filter(dest_v2 => {
                dest_v1._1 < dest_v2._1
              })
            10
          })
          .filter(_ > source)
          .foldLeft(0)(_ + _)
        res
      }).toArray

    a.last
  }

  def benchGraph2(reps: Int) = {
    Utils.mean_std(reps)(() => updatingGraph2())
  }

  def updatingGraph1() = {
    Random.setSeed(seed)
    val adjList = mutable.Map[Int, ListBuffer[(Int, Int)]]()
    val a = Iterator
      .range(0, nEvents)
      .map[Int](_ => {
        val source = Random.nextInt(maxNodes)
        val kind = Random.nextDouble()
        val l = adjList.getOrElseUpdate(source, ListBuffer.empty)
        if (kind < insertionProb) { // Insert
          val dest = Random.nextInt(maxNodes)
          val value = Random.nextInt(100)
          l.append((dest, value))
        } else {
          val len = l.length
          if (len > 0) {
            val idx = Random.nextInt(len)
            l.remove(idx)
          }
        }

        val res = l.iterator
          .map(dest_v1 => {

            l.iterator
              .filter(dest_v2 => {
                dest_v1._1 < dest_v2._1
              })
            10
          })
          .filter(_ > source)
          .foldLeft(0)(_ + _)
        res
      }).toArray

    a.last
  }

  def benchGraph1(reps: Int) = {
    Utils.mean_std(reps)(() => updatingGraph1())
  }
}
