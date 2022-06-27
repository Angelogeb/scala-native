import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.scalanative.annotation.Location.stack
import scala.scalanative.runtime.Local
import scala.util.matching.Regex

trait SimpleParsers {
  type Input

  trait Result[+T] {
    def next: Input
    def map[U](f: (T => U) @stack): Result[U]
    def flatMapWithNext[U](f: (T => Parser[U] @stack) @stack): Result[U]
    def append[U >: T](alt: => Result[U]): Result[U]
  }

  case class Success[+T](result: T, next: Input) extends Result[T] {
    def map[U](f: (T => U) @stack) = Success(f(result), next)
    def flatMapWithNext[U](f: (T => Parser[U] @stack) @stack) = f(result)(next)
    def append[U >: T](alt: => Result[U]) = this
  }

  case class Failure(msg: String, next: Input) extends Result[Nothing] {
    def map[U](f: (Nothing => U) @stack) = this
    def flatMapWithNext[U](f: (Nothing => Parser[U] @stack) @stack) = this
    def append[U](alt: => Result[U]) = alt
  }

  @stack class Parser[+T](val f: (Input => Result[T]) @stack) {
    def apply(in: Input): Result[T] = f(in)

    def flatMap[U](f: (T => Parser[U] @stack) @stack): Parser[U] @stack =
      new Parser((in: Input) => { this(in).flatMapWithNext(f) })

    def map[U](f: (T => U) @stack): Parser[U] @stack =
      new Parser((in: Input) => { this(in).map(f) })

    def |[U >: T](p: (() => Parser[U] @stack) @stack): Parser[U] @stack =
      new Parser((in: Input) => { this(in).append(p()(in)) })

    def ~[U](p: (() => (Parser[U] @stack)) @stack): Parser[Pair[T, U]] @stack =
      this.flatMap(a => p().map(b => (a, b)))


    def ~> [U](p: (() => (Parser[U] @stack)) @stack): Parser[U] @stack =
      this.flatMap(a => p().map(b =>  b))
    def <~ [U](p: (() => (Parser[U] @stack)) @stack): Parser[T] @stack =
      this.flatMap(a => p().map(b => a))
    def ^^ [U](f: (T => U) @stack): Parser[U] @stack = map(f)

  }

  def success[T](v: T): Parser[T] @stack = new Parser(in => Success(v, in))
  def rep[T](p: (() => (Parser[T] @stack)) @stack): Parser[List[T]] @stack = rep1(p) |[List[T]] (() => success(List[T]()))
  def rep1[T](p: (() => (Parser[T] @stack)) @stack): Parser[List[T]] @stack =
    rep1(p, p)

  def rep1[T](first: (() => (Parser[T] @stack)) @stack, p0: (() => (Parser[T] @stack)) @stack): Parser[List[T]] @stack = new Parser(in => {
    val p = p0()
    val elems = new ListBuffer[T]

    @stack def continue(in: Input): Result[List[T]] = {
      val p0 = p
      @stack @tailrec def applyp(in0: Input): Result[List[T]] = p0(in0) match {
        case Success(x, rest) => elems += x ; applyp(rest)
        case e @ Failure(_, _)  => Success(elems.toList, in0)
      }
      applyp(in)
    }

    first()(in) match {
      case Success(x, rest) => elems += x ; continue(rest)
      case ns: Failure      => ns
    }
  })

  def repsep[T](p: () => (Parser[T] @stack) , q: () => (Parser[Any] @stack)): Parser[List[T]] @stack =
    rep1sep(p, q) | (() => success(List()))

  def rep1sep[T](p: () => (Parser[T] @stack), q: () => (Parser[Any] @stack)): Parser[List[T]] @stack = {
    val pp = p()
    val qq = q()
    pp ~[List[T]] (() => rep(() => qq ~> p)) ^^ {case (x, y) => x::y}
  }
}


trait StringParsers extends SimpleParsers {
  type Input = String
  private val EOI = ""
  def lit(expected: String): Parser[String] @stack = new Parser[String](
    (in: String) =>
      if (in == "") {
        if(expected == EOI)
          Success(expected, "")
        else
          Failure("no more input", in)
      } else {
        var i = 0
        val n = expected.length
        if (n > in.length) Failure("expected \'"+expected+"\'", in)
        else {
          while (i < n && in.charAt(i) == expected.charAt(i)) {
            i += 1
          }
          if (i == n) Success(expected, in.substring(n))
          else Failure("expected \'" + expected + "\'", in)
        }
      }
  )

  def regex(r: Regex): Parser[String] @stack = new Parser[String](
    (in: String) => {
      r.findPrefixMatchOf(in) match {
        case Some(matc) => Success(in.substring(0, matc.end), in.substring(matc.end))
        case None => Failure(s"${in} doesn't match regex ${r}", in)
      }
    }
  )

  def decimalNumber: Parser[String] @stack = regex("""(\d+(\.\d*)?|\d*\.\d+)""".r)
  def stringLiteral: Parser[String] @stack = regex(("\""+"""([^"\x00-\x1F\x7F\\]|\\[\\'"bfnrt]|\\u[a-fA-F0-9]{4})*"""+"\"").r)

  val jsonParser = {
    def value: Parser[Any] @stack = obj | (() => arr) | (() => stringLiteral) |
      (() => decimalNumber) | (() => lit("null")) | (() => lit("true")) | (() => lit("false"))
    def obj: Parser[Any] @stack = lit("{") ~>[Any] (() => repsep[Any](() => member, () => lit(","))) <~[Any] (() => lit("}"))
    def arr: Parser[Any] @stack = lit("[") ~>[Any] (() => repsep[Any](() => value, () => lit(","))) <~[Any] (() => lit("]"))
    def member: Parser[Any] @stack = stringLiteral ~[Any] (() => lit(":") ~>[Any] (() => value))
    value
  }


  def eoi = lit(EOI)
}


class ParserCombinators(len: Int) extends StringParsers {
  def oxo = lit("o") ~[String] (() => lit("x")) ~[String] (() => lit("o"))
  def oxos: Parser[Any] @stack =
    ( oxo ~[String] (() => lit("")) ~[Any] (() => oxos)
      | (() => oxo)
      )

  def aaaaa(): Parser[Any] @stack = rep[Any](() => lit("a"))

  var inpt = 0.to(len).map(_ => "ab").mkString

  def `ab*`(): Parser[Any] @stack = (lit("ab") ~[Any] (() => `ab*`())) | (() => lit(""))

  val json = "{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{\"child\":{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}"

  def run() = {
    //
    //    println(aaaaa()(inpt))
    //    println(lit("a")("a"))
    ////    println(repsep[String](() => literal("foo"), () => literal(":"))("foo:foo:foo:foo:foo<<<"))
    //    println(repsep[String](lit("a"), lit(","))("a,a,a,a,a,a"))
    //    println(decimalNumber("419040943"))

    Utils.loop(50, _ => {
//      val js = "{\"message\":\"Validation Failed\",\"errors\":[{\"resource\":\"Issue\",\"field\":\"title\",\"code\":\"missing_field\"}]}"
      `ab*`()(inpt)
    })
  }
}
