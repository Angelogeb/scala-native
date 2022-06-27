import java.io.FileWriter
import java.nio.file.{Files, Paths, Path => JPath}
import scala.collection.mutable
import scala.reflect.internal.util.{BatchSourceFile, Position}
import scala.scalanative.localplugin.LocalPlugin
import scala.tools.nsc.io.{AbstractFile, Path, VirtualDirectory}
import scala.tools.nsc.reporters.{FilteringReporter, StoreReporter}
import scala.tools.nsc.{Global, Settings}

class MyReporter(val settings: Settings) extends FilteringReporter {
  val infos = new mutable.ArrayBuffer[StoreReporter.Info]

  def doReport(pos: Position, msg: String, severity: Severity): Unit = {
    infos += StoreReporter.Info(pos, msg, severity)
  }

  override def reset(): Unit = {
    super.reset()
    infos.clear()
  }
}

object TestLocalPlugin {

  def getSettings = {
    val settings = new Settings
    settings.usejavacp.value = true
    settings.outputDirs.setSingleOutput(new VirtualDirectory("(memory)", None))
    settings
  }

  def getCompiler(settings: Settings) = {
    val reporter = new MyReporter(settings)
    val compiler = new Global(settings, reporter) {
      override protected def computeInternalPhases () {
        super.computeInternalPhases
        for (phase <- new LocalPlugin(this).components)
          phasesSet += phase
      }
    }
    (compiler, reporter)
  }

  def withFileWriter(path: JPath)(f: FileWriter => Unit) = {
    path.getParent.toFile.mkdirs()
    Files.deleteIfExists(path)
    val fw = new FileWriter(path.toFile)
    f(fw)
    fw.close()
  }

  def runDirectory(comp: Global, reporter: MyReporter, testIn: JPath, testOut: JPath) = {
    if (!Files.exists(testOut)) Files.createDirectories(testOut)

    val inDir = Path(testIn.toFile).toDirectory
    val files = inDir.walkFilter(p => p.isDirectory || p.name.endsWith(".scala")).toList

    val inp = files.map(p => new BatchSourceFile(AbstractFile.getFile(p)))

    reporter.reset()
    new comp.Run compileSources inp
    reporter.infos.groupBy(_.pos.source.path).foreach(((path: String, reports: mutable.ArrayBuffer[StoreReporter.Info]) => {
      val testInRelative = testIn.relativize(JPath.of(path))
      val outPath = testOut.resolve(testInRelative)
      withFileWriter(outPath) { fw =>
        for (report <- reports) {
          fw.write(s"[${report.severity}] ${Position.formatMessage(report.pos, report.msg, true)}\n")
        }
      }
    }).tupled)
  }

  def main(args: Array[String]): Unit = {
    val settings = getSettings
    val (comp, reporter) = getCompiler(settings)

    val root = Paths.get(".").toAbsolutePath

    val resources = "localplugin-tests/src/main/resources"

    val names = Seq("sandbox", s"${resources}/typecheck-tests", s"${resources}/captures-tests")

    for (name <- names) {
      val testIn = root.resolve(name)
      val testOut = root.resolve(s"${resources}/test-out/${name}")

      runDirectory(comp, reporter, testIn, testOut)
    }

  }
}
