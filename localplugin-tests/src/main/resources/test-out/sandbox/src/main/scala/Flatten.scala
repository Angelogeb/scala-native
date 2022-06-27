[INFO] Flatten.scala:1: package <empty>{<empty>.type} {
  import scala.scalanative.annotation.Location.stack;
  sealed abstract trait Tree extends scala.AnyRef;
  case class Leaf extends AnyRef with Tree with Product with Serializable {
    <caseaccessor> <paramaccessor> private[this] val v: Int = _;
    <stable> <caseaccessor> <accessor> <paramaccessor> def v: Int = Leaf.this.v{Int};
    def <init>(v: Int): Leaf = {
      Leaf.super.<init>{()Object}(){Object};
      (){Unit}
    }{Unit};
    <synthetic> def copy(v: Int = v{Int}): Leaf = new Leaf{Leaf}{(v: Int)Leaf}(v{Int}){Leaf};
    <synthetic> def copy$default$1: Int = Leaf.this.v{Int};
    override <synthetic> def productPrefix: String = "Leaf"{String("Leaf")};
    <synthetic> def productArity: Int = 1{Int(1)};
    <synthetic> def productElement(x$1: Int): Any = x$1{Int} match {
      case 0{Int(0)} => Leaf.this.v{Int}
      case _{Int} => throw new IndexOutOfBoundsException{IndexOutOfBoundsException}{(x$1: String)IndexOutOfBoundsException}(x$1.toString{()String}(){String}){IndexOutOfBoundsException}{Nothing}
    }{Any};
    override <synthetic> def productIterator: Iterator[Any] = scala.runtime.ScalaRunTime.typedProductIterator{[T](x: Product)Iterator[T]}[Any]{(x: Product)Iterator[Any]}(Leaf.this{Leaf}){Iterator[Any]};
    <synthetic> def canEqual(x$1: Any): Boolean = x$1.$isInstanceOf{[T0]()Boolean}[Leaf]{()Boolean}(){Boolean};
    override <synthetic> def hashCode(): Int = {
      <synthetic> var acc: Int = -889275714{Int(-889275714)};
      acc{Int} = scala.runtime.Statics.mix{(x$1: Int, x$2: Int)Int}(acc{Int}, v{Int}){Int}{Unit};
      scala.runtime.Statics.finalizeHash{(x$1: Int, x$2: Int)Int}(acc{Int}, 1{Int(1)}){Int}
    }{Int};
    override <synthetic> def toString(): String = scala.runtime.ScalaRunTime._toString{(x: Product)String}(Leaf.this{Leaf}){String};
    override <synthetic> def equals(x$1: Any): Boolean = Leaf.this.eq(x$1.asInstanceOf[Object]).||{(x: Boolean)Boolean}(x$1 match {
  case (_: Leaf) => true
  case _ => false
}.&&{(x: Boolean)Boolean}({
      <synthetic> val Leaf$1: Leaf = x$1.asInstanceOf{[T0]=> T0}[Leaf]{Leaf};
      Leaf.this.v.==(Leaf$1.v).&&{(x: Boolean)Boolean}(Leaf$1.canEqual{(x$1: Any)Boolean}(Leaf.this{Leaf}){Boolean}){Boolean}
    }{Boolean}){Boolean}){Boolean}
  };
  <synthetic> object Leaf extends scala.runtime.AbstractFunction1[Int,Leaf] with Serializable {
    def <init>(): Leaf.type = {
      Leaf.super.<init>{()scala.runtime.AbstractFunction1[Int,Leaf]}(){scala.runtime.AbstractFunction1[Int,Leaf]};
      (){Unit}
    }{Unit};
    final override <synthetic> def toString(): String = "Leaf"{String("Leaf")};
    case <synthetic> def apply(v: Int): Leaf = new Leaf{Leaf}{(v: Int)Leaf}(v{Int}){Leaf};
    case <synthetic> def unapply(x$0: Leaf): Option[Int] = if (x$0.=={(x$1: Any)Boolean}(null{Any}){Boolean})
      scala.None{Option[Int]}
    else
      Some.apply{[A](value: A)Some[A]}[Int]{(value: Int)Some[Int]}(x$0.v{Int}){Option[Int]}{Option[Int]};
    <synthetic> private def readResolve(): Object = Leaf{Leaf.type}
  };
  case class Node extends AnyRef with Tree with Product with Serializable {
    <caseaccessor> <paramaccessor> private[this] val l: Tree = _;
    <stable> <caseaccessor> <accessor> <paramaccessor> def l: Tree = Node.this.l{Tree};
    <caseaccessor> <paramaccessor> private[this] val r: Tree = _;
    <stable> <caseaccessor> <accessor> <paramaccessor> def r: Tree = Node.this.r{Tree};
    def <init>(l: Tree, r: Tree): Node = {
      Node.super.<init>{()Object}(){Object};
      (){Unit}
    }{Unit};
    <synthetic> def copy(l: Tree = l{Tree}, r: Tree = r{Tree}): Node = new Node{Node}{(l: Tree, r: Tree)Node}(l{Tree}, r{Tree}){Node};
    <synthetic> def copy$default$1: Tree = Node.this.l{Tree};
    <synthetic> def copy$default$2: Tree = Node.this.r{Tree};
    override <synthetic> def productPrefix: String = "Node"{String("Node")};
    <synthetic> def productArity: Int = 2{Int(2)};
    <synthetic> def productElement(x$1: Int): Any = x$1{Int} match {
      case 0{Int(0)} => Node.this.l{Tree}
      case 1{Int(1)} => Node.this.r{Tree}
      case _{Int} => throw new IndexOutOfBoundsException{IndexOutOfBoundsException}{(x$1: String)IndexOutOfBoundsException}(x$1.toString{()String}(){String}){IndexOutOfBoundsException}{Nothing}
    }{Any};
    override <synthetic> def productIterator: Iterator[Any] = scala.runtime.ScalaRunTime.typedProductIterator{[T](x: Product)Iterator[T]}[Any]{(x: Product)Iterator[Any]}(Node.this{Node}){Iterator[Any]};
    <synthetic> def canEqual(x$1: Any): Boolean = x$1.$isInstanceOf{[T0]()Boolean}[Node]{()Boolean}(){Boolean};
    override <synthetic> def hashCode(): Int = scala.runtime.ScalaRunTime._hashCode{(x: Product)Int}(Node.this{Node}){Int};
    override <synthetic> def toString(): String = scala.runtime.ScalaRunTime._toString{(x: Product)String}(Node.this{Node}){String};
    override <synthetic> def equals(x$1: Any): Boolean = Node.this.eq(x$1.asInstanceOf[Object]).||{(x: Boolean)Boolean}(x$1 match {
  case (_: Node) => true
  case _ => false
}.&&{(x: Boolean)Boolean}({
      <synthetic> val Node$1: Node = x$1.asInstanceOf{[T0]=> T0}[Node]{Node};
      Node.this.l.==(Node$1.l).&&(Node.this.r.==(Node$1.r)).&&{(x: Boolean)Boolean}(Node$1.canEqual{(x$1: Any)Boolean}(Node.this{Node}){Boolean}){Boolean}
    }{Boolean}){Boolean}){Boolean}
  };
  <synthetic> object Node extends scala.runtime.AbstractFunction2[Tree,Tree,Node] with Serializable {
    def <init>(): Node.type = {
      Node.super.<init>{()scala.runtime.AbstractFunction2[Tree,Tree,Node]}(){scala.runtime.AbstractFunction2[Tree,Tree,Node]};
      (){Unit}
    }{Unit};
    final override <synthetic> def toString(): String = "Node"{String("Node")};
    case <synthetic> def apply(l: Tree, r: Tree): Node = new Node{Node}{(l: Tree, r: Tree)Node}(l{Tree}, r{Tree}){Node};
    case <synthetic> def unapply(x$0: Node): Option[(Tree, Tree)] = if (x$0.=={(x$1: Any)Boolean}(null{Any}){Boolean})
      scala.None{Option[(Tree, Tree)]}
    else
      Some.apply{[A](value: A)Some[A]}[(Tree, Tree)]{(value: (Tree, Tree))Some[(Tree, Tree)]}(scala.Tuple2.apply{[T1, T2](_1: T1, _2: T2)(T1, T2)}[Tree, Tree]{(_1: Tree, _2: Tree)(Tree, Tree)}(x$0.l{Tree}, x$0.r{Tree}){(Tree, Tree)}){Option[(Tree, Tree)]}{Option[(Tree, Tree)]};
    <synthetic> private def readResolve(): Object = Node{Node.type}
  };
  abstract trait Flatten extends AnyRef with Runnable {
    def /*Flatten*/$init$(): Unit = {
      (){Unit}
    }{Unit};
    def buildTree(seed: Int): Tree = if (seed.<={(x: Int)Boolean}(0{Int(0)}){Boolean})
      Leaf.apply{(v: Int)Leaf}(0{Int(0)}){Leaf}
    else
      Node.apply{(l: Tree, r: Tree)Node}(Flatten.this.buildTree{(seed: Int)Tree}(seed.-{(x: Int)Int}(1{Int(1)}){Int}){Tree}, Flatten.this.buildTree{(seed: Int)Tree}(seed.-{(x: Int)Int}(1{Int(1)}){Int}){Tree}){Node}{Tree};
    def flattenSC(t: Tree): List[Int] => List[Int] @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack] = t{Tree} match {
      case (v: Int)Leaf((v @ _{Int}){Int}){Leaf} => ((l: List[Int]) => {
        <synthetic> <artifact> val x$1: Int = v{Int};
        l.::{[B >: Int](x: B)List[B]}[Int]{(x: Int)List[Int]}(x$1{Int}){List[Int]}
      }{List[Int]}){List[Int] => List[Int] @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
      case (l: Tree, r: Tree)Node((l @ _{Tree}){Tree}, (r @ _{Tree}){Tree}){Node} => ((ll: List[Int]) => Flatten.this.flattenSC(r).apply{(v1: List[Int])List[Int]}(Flatten.this.flattenSC(l).apply{(v1: List[Int])List[Int]}(ll{List[Int]}){List[Int]}){List[Int]}){List[Int] => List[Int] @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]}
    }{List[Int] => List[Int] @scala.scalanative.annotation.local[scalanative.annotation.Location.Stack]};
    def flattenFC(t: Tree): List[Int] => List[Int] = t{Tree} match {
      case (v: Int)Leaf((v @ _{Int}){Int}){Leaf} => ((l: List[Int]) => {
        <synthetic> <artifact> val x$2: Int = v{Int};
        l.::{[B >: Int](x: B)List[B]}[Int]{(x: Int)List[Int]}(x$2{Int}){List[Int]}
      }{List[Int]}){List[Int] => List[Int]}
      case (l: Tree, r: Tree)Node((l @ _{Tree}){Tree}, (r @ _{Tree}){Tree}){Node} => ((ll: List[Int]) => Flatten.this.flattenFC(r).apply{(v1: List[Int])List[Int]}(Flatten.this.flattenFC(l).apply{(v1: List[Int])List[Int]}(ll{List[Int]}){List[Int]}){List[Int]}){List[Int] => List[Int]}
    }{List[Int] => List[Int]};
    <accessor> val tree: Tree = _;
    <accessor> def tree_=(x$1: Tree): Unit;
    def init(): Unit = {
      enter_1stclass{()Unit}(){Unit};
      <synthetic> val res1: Unit = {
        Flatten.this.tree_={(x$1: Tree)Unit}(Flatten.this.buildTree{(seed: Int)Tree}(10{Int(10)}){Tree}){Unit};
        Utils.repeated{(n: Int)(f: => Any)Unit}(10000{Int(10000)}){(f: => Any)Unit}(Flatten.this.flattenSC(Flatten.this.tree).apply{(v1: List[Int])List[Int]}(scala.collection.immutable.Nil{scala.collection.immutable.Nil.type}){List[Int]}){Unit}
      }{Unit};
      exit_1stclass{()Unit}(){Unit};
      res1{Unit}
    }{Unit};
    def bench(): Unit = {
      enter_1stclass{()Unit}(){Unit};
      <synthetic> val res2: Unit = {
        scala.Predef.println{(x: Any)Unit}(Utils.time{(f: => Any)(Any, Long)}(Utils.repeated{(n: Int)(f: => Any)Unit}(10000{Int(10000)}){(f: => Any)Unit}(Flatten.this.flattenFC(Flatten.this.tree).apply{(v1: List[Int])List[Int]}(scala.collection.immutable.Nil{scala.collection.immutable.Nil.type}){List[Int]}){Unit}){(Any, Long)}){Unit};
        scala.Predef.println{(x: Any)Unit}(Utils.time{(f: => Any)(Any, Long)}(Utils.repeated{(n: Int)(f: => Any)Unit}(10000{Int(10000)}){(f: => Any)Unit}(Flatten.this.flattenSC(Flatten.this.tree).apply{(v1: List[Int])List[Int]}(scala.collection.immutable.Nil{scala.collection.immutable.Nil.type}){List[Int]}){Unit}){(Any, Long)}){Unit}
      }{Unit};
      exit_1stclass{()Unit}(){Unit};
      res2{Unit}
    }{Unit};
    def run(): Unit = {
      Flatten.this.bench{()Unit}(){Unit};
      Flatten.this.bench{()Unit}(){Unit};
      Flatten.this.bench{()Unit}(){Unit};
      Flatten.this.bench{()Unit}(){Unit};
      Flatten.this.bench{()Unit}(){Unit}
    }{Unit}
  }
}
import scala.scalanative.annotation.Location.stack
^
