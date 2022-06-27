package scala.scalanative.localplugin

import scala.collection.mutable
import scala.language.implicitConversions
import scala.tools.nsc.Global
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.symtab.Flags
import scala.tools.nsc.transform.{Transform, TypingTransformers}

abstract class LocalInferPhase[G <: Global with Singleton](val global: G) extends PluginComponent with Transform with
  TypingTransformers with LocalUtils {
  // inherits abstract value `global` and class `Phase` from Transform

  import global._
  import location._

  override def description = "Escape check phase"

  val phaseName: String = "escape"

  protected def newTransformer(unit: CompilationUnit): Transformer =
    new LocalLetInserter(unit) // EscTransformer(unit)

  class LocalLetInserter(unit: CompilationUnit) extends TypingTransformer(unit) {

    var typeMap: mutable.Map[Tree, Type] = _

    override def transformUnit(unit: global.CompilationUnit): Unit = {
      super.transformUnit(unit)
      // reporter.echo(unit.body.pos, show(unit.body, false))
    }

    var allocates = false

    def withCallsSecondClass[A](value: Boolean)(f: => A): A = {
      val saved = allocates
      try {
        allocates = value
        f
      } finally allocates = saved
    }

    def addEnterExit(tree: Tree) = {
      val sym: Symbol = currentOwner
        .newValue(newTermName(unit.fresh.newName("res")), tree.pos, Flags.SYNTHETIC)
        .setInfo(tree.tpe)

      val vd = localTyper.typed(ValDef(sym, tree))
      val id = localTyper.typed(Ident(sym))
      val enter = localTyper.typed(Apply(Enter1stClass))
      val exit = localTyper.typed(Apply(Exit1stClass))

      localTyper.typedPos(tree.pos) {
        Block(
          List(enter, vd, exit),
          id
        )
      }
    }

    override def transform(tree: Tree): Tree = {
      tree match {
        case Function(vparams, body) =>
          allocates = allocates || tree.tpe.hasAnnotation(MarkerLocal) || tree.symbol.hasAnnotation(MarkerLocal)
          atOwner(tree.symbol) {
            withCallsSecondClass(value = false) {
              val tp = tree.tpe
              val body1 = transform(body)
              val resTpe = tp.withoutAnnotations match {
                case foo @ TypeRef(pre, sym, args) => {
                  if (sym.fullNameString.startsWith("scala.Function0")) args(0)
                  else args(1)
                }
              }
              val newBody = if (!resTpe.hasAnnotation(MarkerLocal) && allocates) addEnterExit(body1) else body1
              val newF = treeCopy.Function(tree, vparams, newBody)
              checkCaptures(newF)
              if (tp.hasAnnotation(MarkerLocal)) {
                // We move the annotation to the symbol so later phases
                // in NirGenExpr can lookup symbols of Function to insert
                // localalloc instructions
                tree.symbol.addAnnotation(MarkerLocal)
              }
              newF
            }
          }

        case dd @ DefDef(mods, name, tparams, vparamss, tpt, rhs) if !dd.symbol.isSynthetic =>
          atOwner(tree.symbol) {
            withCallsSecondClass(value = false) {
              checkCaptures(tree)
              val transformedRhs = transform(rhs)
              val newrhs = if (!tpt.tpe.hasAnnotation(MarkerLocal) && allocates) addEnterExit(transformedRhs) else transformedRhs

              treeCopy.DefDef(tree, mods, name, tparams, vparamss, tpt, newrhs)
            }
          }

        case Apply(fun, args) =>
          val newFun = transform(fun)
          val newArgs = args.map(transform)
          val tp = tree.tpe
          allocates = allocates || tp.hasAnnotation(MarkerLocal)
          treeCopy.Apply(tree, newFun, newArgs)

        case _ => super.transform(tree)
      }
    }

    implicit def tupled[T1, T2, O](f: (T1, T2) => O): ((T1, T2)) => O = f.tupled

    private def checkCaptures(tree: global.Tree) = {
      val fv = FreeVarTraverser.freeVarsOf(tree)
      val treeRegion = Location.of(tree)
      val escapingFv = fv.map(sym => (sym, Location.of(sym))).flatMap {
        case (sym, symRegion) if symRegion.outlives(treeRegion) => Some((sym, symRegion))
        case _ => None
      }

      escapingFv.foreach { (sym: Symbol, region: Location) =>
        reporter.error(tree.pos, s"Method/Function in region ${Location.nameOf(treeRegion)} " +
          s"outlives captured symbol [${sym.nameString}] living in region ${Location.nameOf(region)}")
      }
    }
  }

  // Adapted from Delambdafy
  class FreeVarTraverser extends Traverser {
    val freeVars = mutable.LinkedHashSet[Symbol]()
    val declared = mutable.LinkedHashSet[Symbol]()

    override def traverse(tree: Tree) = {
      tree match {
        case Function(args, _) =>
          args foreach {arg => declared += arg.symbol}
        case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          vparamss.flatten.foreach {arg => declared += arg.symbol}
          declared += tree.symbol
        case ValDef(_, _, _, _) =>
          declared += tree.symbol
        case _: Bind =>
          declared += tree.symbol
        case Ident(_) =>
          val sym = tree.symbol
          if ((sym != NoSymbol) && sym.isLocalToBlock && sym.isTerm /*&& !sym.isMethod*/ && !declared.contains(sym)) freeVars += sym
        case _ =>
      }
      super.traverse(tree)
    }
  }
  object FreeVarTraverser extends FreeVarTraverser {
    def freeVarsOf(function: Tree) = {
      val freeVarsTraverser = new FreeVarTraverser
      freeVarsTraverser.traverse(function)
      freeVarsTraverser.freeVars
    }
  }
}
