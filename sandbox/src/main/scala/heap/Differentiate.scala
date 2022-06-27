package heap
import Linear.{grad, loss, relu}
import Shift.reset

import scala.language.implicitConversions
import scala.scalanative.annotation.Location.stack

 class StackTuple2[T1, T2](val _1: T1 , val _2: T2 )

 class Shift(val fun: ((Tensor  => Unit)  => Unit) ) {
  @inline def map(f: Tensor  => Tensor ): Shift  = {
    new Shift(k => fun(x => k(f(x))))
  }

  @inline def flatMap(f: Tensor  => Shift ): Shift  = {
    new Shift(k => fun(x => f(x).fun(k)))
  }
}
object Shift {
  def reset(c: Shift ) = c.fun(_ => ())
}

object Loop {
  @inline def loop(n: Int, body: (Int => Unit) ) = {
    var i = 0
    while (i < n) {
      body(i)
      i += 1
    }
  }
}
import Loop.loop

 class Tensor(val shape: List[Int], val data: Array[Float] , val grad: Array[Float] ) {
  val numel: Int = data.length
  val s2 = if (shape.length > 1) shape(1) else 0

  @inline def apply(i: Int) = {
    data(i)
  }

  @inline def apply(i1: Int, i2: Int) = {
    data(i1 * s2 + i2)
  }

  @inline def update(i: Int, v: Float) = {
    data(i) = v
  }

  @inline def gadd(i: StackTuple2[Integer, Integer] , v: Float) = {
    grad(i._1 * s2 + i._2) += v
  }

  override def toString: String = shape match {
    case s1 :: Nil => s"[${data.asInstanceOf[Array[Float]].mkString(", ")}]"
    case os :: is :: Nil =>
      s"[${data.asInstanceOf[Array[Float]].grouped(is).map(a => s"[${a.mkString(",")}]").mkString("\n ")}]"
    case _ => ???
  }

}

object Tensor {
  @inline def argmax(t: Tensor ) = {
    val a = t.data
    var res = a(0)
    var resi = 0

    loop(t.data.length, i => {
      if (a(i) > res) {
        res = a(i)
        resi = i
      }
    })
    resi
  }

  @inline def sum_exp(t: Tensor ) = {
    val a = t.data
    var res = 0f
    var i = 0
    val l = t.data.length
    while (i < l) {
      res += scala.math.exp(a(i)).toFloat
      i += 1
    }
    res
  }

  def randn(shape: List[Int]): Tensor = {
    val fanIn = shape.head
    val fanOut = if (shape.length > 1) shape(1).toFloat else 1f
    val xavierRange = scala.math.sqrt(6f / (fanIn + fanOut)).toFloat

    val sz: Int = shape.product
    val a = new Array[Float](sz)
    var i = 0
    while (i < sz) {
      a(i) = scala.util.Random.nextFloat() * 2f * xavierRange - xavierRange
      i += 1
    }

    val ag = new Array[Float](sz)
    new Tensor(shape, a, ag)
  }

  def matmuladd(W: Tensor, x: Tensor , b: Tensor): Tensor  = {
    val rows = W.shape(0)
    val cols = W.shape(1)

     val outA = new Array[Float](rows)
     val outAG = new Array[Float](rows)
    val ot = new Tensor(rows :: Nil, outA, outAG)

    loop(rows, r => {
      var accum = 0f
      loop(cols, c => {
        accum += W(r, c) * x(c)
      })
      ot(r) = accum + b(r)
    })

    ot
  }

  def `∇matmuladd`(g: Array[Float] , lhs: Tensor, rhs: Tensor , b: Tensor) = {
    val rows = lhs.shape(0)
    val cols = lhs.shape(1)
    loop(rows, r => {
      loop(cols, c => {
         val v1 = new Integer(r)
         val v2 = new Integer(c)
         val idx = new StackTuple2(v1, v2)
        lhs.gadd(idx, rhs(c) * g(r))
      })
      b.grad(r) += g(r)
    })
  }
}

class Linear(shape: (Int, Int), bias: Boolean = true) {
  val W = Tensor.randn(shape._1 :: shape._2 :: Nil)
  val b = Tensor.randn(shape._1 :: Nil)

  def apply(x: Tensor): Shift  = new Shift(
    k => {
      val outT = Tensor.matmuladd(W, x, b)
      k(outT)
      Tensor.`∇matmuladd`(outT.grad, W, x, b)
    })
}

object Linear {
  def relu(t: Tensor ): Shift  = new Shift(k => {
    val sz = t.numel
     val outA = new Array[Float](sz)
     val outAG = new Array[Float](sz)

    loop(sz, i => {
      val v = t(i)
      outA(i) = if (v > 0) v else 0
    })

    val outT = new Tensor(t.shape, outA, outAG)
    k(outT)

    loop(sz, i => {
      t.grad(i) = if (t(i) > 0) outAG(i) else 0
    })
  })

  def loss(target: Tensor, pred: Tensor ): Shift  = new Shift(
    k => {
      val cl = Tensor.argmax(target)
       val lossA = new Array[Float](1)
       val lossAG = new Array[Float](1)
      lossA(0) = -pred.data(cl) + math.log(Tensor.sum_exp(pred)).toFloat

      val lossT = new Tensor(1::Nil, lossA, lossAG)
      k(lossT)

      loop(pred.data.length, i => {
        pred.grad(i) = pred(i) - target(i)
      })
    })

  def grad(f: Tensor => Shift )(x: Tensor) = reset(f(x))

  def apply(shape: (Int, Int)) = new Linear(shape)
}

class MLP(val shapes: List[(Int, Int)]) {
  val l1: Linear = Linear(shapes.head)
  val l2: Linear = Linear(shapes(1))
  val l3: Linear = Linear(shapes(2))

  def apply(x: Tensor): Shift  = {
    for {
      z1 <- l1(x)
      h1 <- relu(z1)
      z2 <- l2(h1)
      h2 <- relu(z2)
      o  <- l3(h2)
    } yield o
  }
}

class Differentiate(epochs: Int) {

  def optimize(p: Tensor, η: Float): Unit = {
    var i = 0
    val l = p.numel
    while (i < l) {
      p.data(i) -= η * p.grad(i)
      p.grad(i) = 0
      i += 1
    }
  }

  val mlp = new MLP((512, 28 * 28) :: (512, 512) :: (10, 512) :: Nil)
  val x = (0 until 28 * 28).map(_ => scala.util.Random.nextFloat()).toArray
  val y = new Array[Float](10)
  val xt = new Tensor(28*28::Nil, x, null)
  val yt = new Tensor(10::Nil, y, null)
  val data: List[(Tensor, Tensor)] = (xt, yt)::Nil
  y(4) = 1f
  val η = 0.01f
  val pars = List(mlp.l1.W, mlp.l1.b, mlp.l2.W, mlp.l2.b, mlp.l3.W, mlp.l3.b)


  def run() = {
    var finalLoss = 0f

    for (_ <- 0 until epochs) {
      for ((x, y) <- data) {
        grad { x =>
          for {
            o <- mlp(x)
            l <- loss(y, o)
          } yield {

            finalLoss = l.data(0)
            l
          }
        }(x)

        pars.foreach(optimize(_, η))
      }
    }
    println(finalLoss)
  }

  def bench(rep: Int) = {
    Utils.mean_std(rep)(() => run())
  }
}
