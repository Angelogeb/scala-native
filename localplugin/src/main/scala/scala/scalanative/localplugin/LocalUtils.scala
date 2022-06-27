package scala.scalanative.localplugin

import scala.tools.nsc.Global

trait LocalUtils {
  val global: Global

  import global._

  object LocalAnnotation {
    def unapply(tpe: Type): Option[Type] = tpe match {
      case TypeRef(pre, sym, args) if sym == MarkerLocal => Some(args.head)
      case _ => None
    }

    def unapply(anno: AnnotationInfo): Option[Type] = anno match {
      case AnnotationInfo(LocalAnnotation(region), _, _) => Some(region)
      case _ => None
    }
  }

  object location {
    /**
     * Emulate Opaque types
     * Location instances should be created only through `Location.of`
     */
    trait Location {
      private[location] val tpe: Type

      def containedIn(loc: Location): Boolean = tpe <:< loc.tpe

      def outlives(loc: Location): Boolean = !containedIn(loc)
      def isHeap: Boolean = tpe.isNothing
    }

    object Location {

      private[this] def LocationT(tp: Type): Location = {
        new Location {
          override val tpe: Type = tp
          override def toString: String = tpe.toString()
        }
      }

      val Stack: Location = LocationT(definitions.AnyTpe)
      val Heap: Location = LocationT(definitions.NothingTpe)

      def nameOf(l: Location): String = l.tpe match {
        case definitions.AnyTpe => "stack"
        case definitions.NothingTpe => "heap"
        case _ => l.tpe.toString
      }

      /**
       * This is for getting annotations from method symbols.
       * Since method types are defined by parameters and return type
       * annotations are on the sumbol:
       *
       * @local[Region] def foo(p1: T1, p2: T2): O = ???
       *
       *
       *                The type of the above is equivalent to ((T1, T2) => O) @local[Region]
       *
       */
      def of(sym: Symbol): Location = {
        // For Regions the Location, if absent is the one in their inner type
        // FIXME: proper lookup and check if they are annotated first
        if (sym.tpe.toString.startsWith("scala.scalanative.annotation.Region")) {
          return LocationT(global.typer.typedType(Select(Ident(sym), TypeName("T"))).tpe)
        }

        val regions = sym.annotations.flatMap {
          case LocalAnnotation(region) => Some(region)
          case _ => None
        }
        regions match {
          case region :: Nil => LocationT(region)
          case Nil => of(sym.tpe)
          case _ => ???
        }
      }

      def of(tree: Tree): Location = tree match {
        case dd: DefDef => of(dd.symbol)
        case _ => of(tree.tpe)
      }

      val baseTpes = Set("Int", "Integer")
      def of(tpe: Type): Location = {
        if (baseTpes(tpe.withoutAnnotations.toString)) return Heap
        val annos = tpe.annotations.filter(_.matches(MarkerLocal))
        val localAnnotation = annos.flatMap {
          LocalAnnotation.unapply(_)
        }
        localAnnotation match {
          case region :: Nil => LocationT(region)
          case Nil => Heap
          case _ => ???
        }
      }

      def withLocation(tpe: Type, loc: Location): Type = {
        tpe.withAnnotation(AnnotationInfo.marker(appliedType(MarkerLocal.tpe, loc.tpe)))
      }

      def lub(ls: List[Location]): Location = LocationT(global.lub(ls.map(_.tpe)))

      def ofBinding(vd: ValDef, typer: analyzer.Typer): Option[Location] = {
        val possibleStackAnno: List[Tree] = vd.mods.annotations.flatMap {
          case a@Apply(Select(New(Ident(TypeName("stack"))), _), _) => Some(a)
          case a@Apply(Select(New(Select(_, TypeName("stack"))), _), _) => Some(a)
          case a@Apply(Select(New(Ident(TypeName("local"))), _), _) => Some(a)
          case a@Apply(Select(New(Select(_, TypeName("local"))), _), _) => Some(a)
          case a@Apply(Select(New(AppliedTypeTree(Ident(TypeName("local")), _)), _), _) => Some(a)
          case _ => None
        }

        possibleStackAnno match {
          case app :: Nil =>
            typer.typed(app).tpe match {
              case LocalAnnotation(region) => Some(LocationT(region))
              case _ => None
            }
          case Nil => None
          case _ =>
            reporter.error(vd.pos, "Too many annotations in this binding")
            None
        }
      }

    }
  }

  lazy val MarkerLocal: Symbol = rootMirror.getRequiredClass("scala.scalanative.annotation.local")

  lazy val LocalModule = rootMirror.getRequiredModule(
    "scala.scalanative.runtime.Local"
  )
  lazy val Enter1stClass = definitions.getMember(LocalModule, TermName("enter_1stclass"))
  lazy val Exit1stClass = definitions.getMember(LocalModule, TermName("exit_1stclass"))

}