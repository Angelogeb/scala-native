package object Utils {
  // nanoseconds
  @inline def timed(f:() => Unit) = {
    val start = System.nanoTime()
    val res   = f()
    val time = (System.nanoTime() - start).toDouble
    time
  }

  @inline def loop(n: Int, body: Int => Unit) = {
    var i = 0
    while (i < n) {
      body(i)
      i += 1
    }
  }

  @inline def mean_std(n: Int)(f: () => Unit) = {
    // Warmup
    val foo @ (_, _, _) = (timed(f), timed(f), timed(f))

    // Run
    var i = 0
    var tot_time = 0d
    var timesqrd = 0d
    while (i < n) {
      val time = timed(f)
      tot_time += time
      timesqrd += time * time
      i += 1
    }

    val mean = tot_time / n.toDouble
    val stdev = Math.sqrt(n * timesqrd - Math.pow(tot_time, 2)) / n

    val res = new Array[Double](3)
    res(0) = mean
    res(1) = stdev
    res
  }
}
