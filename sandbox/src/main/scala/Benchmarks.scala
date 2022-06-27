import scala.scalanative.annotation.Location.stack
import scala.util.Random
object Benchmarks {

  val usage =
    """  Usage: benchmarks [--n N] name

  name: {flatten | iterator}
  n: number of repetitions""".stripMargin


  val flattenReps = 10000000
  val flattenHeight = 5
  def flatten1 = {
    val run = new Flatten(flattenHeight) {}
    run.init()
    run.benchFC(flattenReps)
  }

  def flatten2 = {
    val run = new Flatten(flattenHeight) {}
    run.init()
    run.benchSC(flattenReps)
  }

  val mlpReps = 5
  val mlpEpochs = 20
  def mlp1 ={
    val fc = new heap.Differentiate(mlpEpochs)
    fc.bench(mlpReps)
  }

  def mlp2 = {
    val sc = new Differentiate(mlpEpochs)
    sc.bench(mlpReps)
  }

  val graphReps = 50
  val graphEvents = 50000
  def graph1 = (new IteratorExamples(graphEvents, maxNodes = 1000, insertionProb = 0.55)).benchGraph1(graphReps)
  def graph2 = (new IteratorExamples(graphEvents, maxNodes = 1000, insertionProb = 0.55)).benchGraph2(graphReps)

  def incBy1(i: Int): (Int => Int)        = v => v + i
  def incBy2(i: Int): (Int => Int) @stack = v => v + i

  val hotloopReps = 100000
  def curry1 = {
    val run = (_: Int) => {
      val plus10 = incBy1(10)
      //      plus10(100)
    }
    val body1 = () => Utils.loop(1000, run)
    Utils.mean_std(hotloopReps)(() => body1())
  }
  def curry2 = {
    val run = (_: Int) => {
      val plus10 = incBy2(10)
      //      plus10(100)
    }
    val body2 = () => Utils.loop(1000, run)
    Utils.mean_std(hotloopReps)(() => body2())
  }

  val filterSz = 50
  val filterReps = 50000
  def filter1 = {
    val bench = new heap.Filter(filterSz)
    bench.init()
    bench.filterSC(filterReps)
  }
  def filter2 = {
    val bench = new Filter(filterSz)
    bench.filterSC(filterReps)
  }

  val parserSlen = 70
  val parserReps = 100
  def parser1 = {
    val bench = new heap.ParserCombinators(parserSlen)
    Utils.mean_std(parserReps)(() => bench.run())
  }

  def parser2 = {
    val bench = new ParserCombinators(parserSlen)
    Utils.mean_std(parserReps)(() => bench.run())
  }

  def main(args: Array[String]): Unit = {
    Random.setSeed(42)
    if (args.isEmpty) println(usage)
    val bench = args.head

    val times: Array[Double] = bench match {
      case "flatten1" => flatten1
      case "flatten2" => flatten2
      case "mlp1"     => mlp1
      case "mlp2"     => mlp2
      case "graph1"     => graph1
      case "graph2"     => graph2
      case "curry1" => curry1
      case "curry2" => curry2
      case "filter1" => filter1
      case "filter2" => filter2
      case "parser1" => parser1
      case "parser2" => parser2
      case _ => println("unknown command"); new Array[Double](2)
    }

    Console.err.println(s"${bench.substring(0, bench.length - 1)}, ${bench.last}, ${times(0)}, ${times(1)}")
  }
}

