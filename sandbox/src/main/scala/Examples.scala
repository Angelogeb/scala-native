import scala.scalanative.annotation.Location.stack

object Examples {
    // `incBy` returns the closure on the stack
    def incBy(v: Int): (Int => Int) @stack = x => x + v

    def appf(f: Int => Int, x: Int) = f(x)
    def apps(f: (Int => Int) @stack, x: Int) = f(x)

    def nested(f: Int => (Int => Int)) = f(10)(12)

    // It is not possible to declare `stack` variables
    // var x: (Int => Int) @stack = null
    // @stack var xx = (i: Int) => i + 5


    def run = {
        val f /*: (Int => Int) @stack */ = incBy(10)

        // The following is ill-typed, uncomment to test
        // appf(f, 2)

        // This application is well-typed since `apps` accepts `@stack`
        apps(f, 4)

        // In this application the closure is allocated on the stack
        apps(i => i * 5, 10)

        // It is possible to build a closure on the heap
        val clo = (i: Int) => i * 5
        // The application is welltyped because T @heap <: T @stack
        apps(clo, 10)

        // The following application is ill-typed
        // `nested` requires for the closure returned by the argument
        // to be heap qualified
//        nested(v => f)

        @stack val twiceCapturesF = (x: Int) => f(x) * 2

        // The following is ill-typed
        // val illcapture = (x: Int) => f(x) * 2
    }
    def main(args: Array[String]) = {
        println("Hello world!")
    }

}
