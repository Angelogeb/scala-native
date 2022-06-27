package scala.scalanative
package localplugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._

abstract class AnnotationCheckerBuilder[G <: Global with Singleton] extends LocalUtils {
  val global: G

  import global._
  import location._

  private[this] def isSecondClass(tpe: Type): Boolean = tpe.annotations.exists(_ matches MarkerLocal)

  object checker extends AnnotationChecker {
    override def isActive(): Boolean = global.phase.id <= 5 /* Our escape phase is 5 */

    override def annotationsConform(tpe1: Type, tpe2: Type): Boolean = {
      if (!isActive) true
      else Location.of(tpe1).containedIn(Location.of(tpe2))
    }

    override def annotationsLub(tp: Type, ts: List[Type]): Type = {
      Location.withLocation(
        tp,
        Location.lub(
          Location.of(tp)::ts.map(Location.of(_))
        )
      )
    }

//    override def annotationsGlb(tp: Type, ts: List[Type]): Type = ???

    override def adaptBoundsToAnnotations(bounds: List[TypeBounds], tparams: List[Symbol], targs: List[Type]): List[TypeBounds] = {
      targs.zip(bounds).map(((arg: Type, bounds: TypeBounds) => {
        if (isSecondClass(arg)) {
          TypeBounds(bounds.lowerBound, bounds.upperBound.withAnnotation(AnnotationInfo(MarkerLocal.tpe, Nil, Nil)))
        } else bounds
      }).tupled)
    }

  }

  object plugin extends analyzer.AnalyzerPlugin {

    override def pluginsTypeSig(tpe: Type, typer: analyzer.Typer, defTree: Tree, pt: Type): Type = defTree match {

      case ValDef(mods, name, tpt, rhs)
        if mods.hasAnnotationNamed(TypeName("local")) && !tpt.tpe.hasAnnotation(MarkerLocal) =>
        reporter.error(defTree.pos, "Only immediate 2nd-class introduction terms are supported in local bindings")
        tpe
      case ValDef(mods, name, tpt, rhs) if mods.isMutable && !Location.of(tpe).isHeap =>
        reporter.error(defTree.pos, "Stack variables are not allowed")
        tpe
      case _ => tpe
    }

    val stackPrimitives = Set("Array", "Integer", "Float")

    override def pluginsTyped(tpe: Type, typer: analyzer.Typer, tree: Tree, mode: Mode, pt: Type): Type = {
      if (typer.context.tree.symbol != null &&
            (typer.context.tree.symbol.isCaseApplyOrUnapply ||
              typer.context.tree.symbol.isCaseCopy)) {
        return if (pt.isWildcard) tpe else pt
      }

      tree match {
        case Function(vparams, body) =>
          if (pt.hasAnnotation(MarkerLocal) && tpe <:< pt) {
            // function term in 2nd-class argument position or return position
            // inferred 2nd-class
            pt
          } else typer.context.tree match {
            // function as rhs of local binding
            // @local val fn = (e: T) => ...
            case vd @ ValDef(mods, name, tpt, rhs) =>
              val location = Location.ofBinding(vd, typer)
              location match {
                case Some(region) => Location.withLocation(tpe, region)
                case None => tpe
              }
            case _ => tpe
          }
        case Apply(Select(New(foo), termNames.CONSTRUCTOR), args) if stackPrimitives.exists(prim => foo.toString.contains(prim)) /* <- FXIME */=>
          if (pt.hasAnnotation(MarkerLocal) && tpe <:< pt) {
            pt
          } else typer.context.tree match {
            // rhs of local binding
            // @local val fn = new Array/Integer/Float
            case vd @ ValDef(mods, name, tpt, rhs) =>
              val location = Location.ofBinding(vd, typer)
              location match {
                case Some(region) =>
                  tree.updateAttachment(DelambdafyTarget)
                  Location.withLocation(tpe, region)
                case None => tpe
              }
            case _ => tpe
          }
        case _ => tpe
      }
    }
  }

}


class LocalPlugin(val global: Global) extends Plugin {
  val name = "local"
  val description = "Support for stack allocated function in Scala Native"
  val components: List[PluginComponent] = if (options contains "enable") List(escPhase) else Nil

  val annoCheckerBuilder = new AnnotationCheckerBuilder[global.type] {
    val global = LocalPlugin.this.global
  }

  if (options contains "enable") {
    global.addAnnotationChecker(annoCheckerBuilder.checker)
    global.analyzer.addAnalyzerPlugin(annoCheckerBuilder.plugin)
  }

  object escPhase extends LocalInferPhase[global.type](global) {
    override val runsAfter = List("typer")
    override val runsBefore = List("patmat")
  }

  override def init(options: List[String], error: String => Unit): Boolean = options forall {
    case "enable" => true
    case _ => false
  }

  override val optionsHelp: Option[String] = Some("-P:local:enable")

}
