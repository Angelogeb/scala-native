import scala.scalanative.annotation.Location.stack

sealed trait Tree
case class Leaf(v: Int) extends Tree
case class Node(l: Tree, v: Int, r: Tree) extends Tree

abstract class Flatten(binTreeHeight: Int) {

  def buildTree(seed: Int): Tree =
    if (seed <= 0) Leaf(0)
    else Node(buildTree(seed - 1), seed, buildTree(seed - 1))

  def flattenSC(t: Tree): (List[Int] => List[Int])@stack = t match {
    case Leaf(v) => l => v :: l
    case Node(l, v, r) =>
      val rf = flattenSC(r)
      val lf = flattenSC(l)
      ll => v:: rf(lf(ll))
  }

  def flattenFC(t: Tree): (List[Int] => List[Int]) = t match {
    case Leaf(v) => l => v :: l
    case Node(l, v, r) =>
      val rf = flattenFC(r)
      val lf = flattenFC(l)
      ll => v:: rf(lf(ll))
  }

  var tree: Tree = _
  def init() = {
    tree = buildTree(binTreeHeight)
    Utils.loop(10, _ => {
      flattenSC(tree)(Nil)
    })
  }

  def benchFC(repeat: Int) = {
    Utils.mean_std(repeat)(() => {
      flattenFC(tree)(Nil)
    })
  }

  def benchSC(repeat: Int) = {
    Utils.mean_std(repeat)(() => {
      flattenSC(tree)(Nil)
    })
  }
}
