package heap
import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.scalanative.annotation.Location.stack
import scala.scalanative.runtime.Local
import scala.util.matching.Regex

trait SimpleParsers {
  type Input

  trait Result[+T] {
    def next: Input
    def map[U](f: (T => U) ): Result[U]
    def flatMapWithNext[U](f: (T => Parser[U] ) ): Result[U]
    def append[U >: T](alt: => Result[U]): Result[U]
  }

  case class Success[+T](result: T, next: Input) extends Result[T] {
    def map[U](f: (T => U) ) = Success(f(result), next)
    def flatMapWithNext[U](f: (T => Parser[U] ) ) = f(result)(next)
    def append[U >: T](alt: => Result[U]) = this
  }

  case class Failure(msg: String, next: Input) extends Result[Nothing] {
    def map[U](f: (Nothing => U) ) = this
    def flatMapWithNext[U](f: (Nothing => Parser[U] ) ) = this
    def append[U](alt: => Result[U]) = alt
  }

   class Parser[+T](val f: (Input => Result[T]) ) {
    def apply(in: Input): Result[T] = f(in)

    def flatMap[U](f: (T => Parser[U] ) ): Parser[U]  =
      new Parser((in: Input) => { this(in).flatMapWithNext(f) })

    def map[U](f: (T => U) ): Parser[U]  =
      new Parser((in: Input) => { this(in).map(f) })

    def |[U >: T](p: (() => Parser[U] ) ): Parser[U]  =
      new Parser((in: Input) => { this(in).append(p()(in)) })

    def ~[U](p: (() => (Parser[U] )) ): Parser[Pair[T, U]]  =
      this.flatMap(a => p().map(b => (a, b)))


    def ~> [U](p: (() => (Parser[U] )) ): Parser[U]  =
      this.flatMap(a => p().map(b =>  b))
    def <~ [U](p: (() => (Parser[U] )) ): Parser[T]  =
      this.flatMap(a => p().map(b => a))
    def ^^ [U](f: (T => U) ): Parser[U]  = map(f)

  }

  def success[T](v: T): Parser[T]  = new Parser(in => Success(v, in))
  def rep[T](p: (() => (Parser[T] )) ): Parser[List[T]]  = rep1(p) |[List[T]] (() => success(List[T]()))
  def rep1[T](p: (() => (Parser[T] )) ): Parser[List[T]]  =
    rep1(p, p)

  def rep1[T](first: (() => (Parser[T] )) , p0: (() => (Parser[T] )) ): Parser[List[T]]  = new Parser(in => {
    val p = p0()
    val elems = new ListBuffer[T]

     def continue(in: Input): Result[List[T]] = {
      val p0 = p
       @tailrec def applyp(in0: Input): Result[List[T]] = p0(in0) match {
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

  def repsep[T](p: () => (Parser[T] ) , q: () => (Parser[Any] )): Parser[List[T]]  =
    rep1sep(p, q) | (() => success(List()))

  def rep1sep[T](p: () => (Parser[T] ), q: () => (Parser[Any] )): Parser[List[T]]  = {
    val pp = p()
    val qq = q()
    pp ~[List[T]] (() => rep(() => qq ~> p)) ^^ {case (x, y) => x::y}
  }
}


trait StringParsers extends SimpleParsers {
  type Input = String
  private val EOI = ""
  def lit(expected: String): Parser[String]  = new Parser[String](
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

  def regex(r: Regex): Parser[String]  = new Parser[String](
    (in: String) => {
      r.findPrefixMatchOf(in) match {
        case Some(matc) => Success(in.substring(0, matc.end), in.substring(matc.end))
        case None => Failure(s"${in} doesn't match regex ${r}", in)
      }
    }
  )

  def decimalNumber: Parser[String]  = regex("""(\d+(\.\d*)?|\d*\.\d+)""".r)
  def stringLiteral: Parser[String]  = regex(("\""+"""([^"\x00-\x1F\x7F\\]|\\[\\'"bfnrt]|\\u[a-fA-F0-9]{4})*"""+"\"").r)

  val jsonParser = {
    def value: Parser[Any]  = obj | (() => arr) | (() => stringLiteral) |
      (() => decimalNumber) | (() => lit("null")) | (() => lit("true")) | (() => lit("false"))
    def obj: Parser[Any]  = lit("{") ~>[Any] (() => repsep[Any](() => member, () => lit(","))) <~[Any] (() => lit("}"))
    def arr: Parser[Any]  = lit("[") ~>[Any] (() => repsep[Any](() => value, () => lit(","))) <~[Any] (() => lit("]"))
    def member: Parser[Any]  = stringLiteral ~[Any] (() => lit(":") ~>[Any] (() => value))
    value
  }


  def eoi = lit(EOI)
}


class ParserCombinators(len: Int) extends StringParsers {
  def oxo = lit("o") ~[String] (() => lit("x")) ~[String] (() => lit("o"))
  def oxos: Parser[Any]  =
    ( oxo ~[String] (() => lit("")) ~[Any] (() => oxos)
      | (() => oxo)
      )

  def aaaaa(): Parser[Any]  = rep[Any](() => lit("a"))

  var inpt = 0.to(len).map(_ => "ab").mkString

  def `ab*`(): Parser[Any]  = (lit("ab") ~[Any] (() => `ab*`())) | (() => lit(""))

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
