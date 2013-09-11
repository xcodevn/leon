package leon.solvers.lemmafilter.mash

import java.io._
import scala.io._

object MaSh {
  /*
   * This is a low-level wrapper for MaSh
   * 
   * Interacting with MaSh by using command line and temp files
   */
  import scala.sys.process._
  import leon._

  // create new reporter cause we don't use LeonContext
  // val reporter = new DefaultReporter()

  var isOk = true

  def getEnv(name: String) = {
    try {
      sys.env(name)
    } catch {
      case _: Throwable =>
        // reporter.error("Can NOT read " + name + " env variables")
        // reporter.info("Disabled mash module")
        isOk = false // after setting this varible mash will be disable
        ""
    }
  }

  val command = getEnv("MASH_DIR") + "/src/mash.py"
  val MaShHome = {
    val path = getEnv("MASH_HOME")
    if (isOk)
      ("mkdir -p " + path).!!
    path
  }

  /* Remove every thing related with Mash from file system */
  def unlearn = {
    // reporter.info("MaSh unlearn")
    if (isOk) {
      // reporter.info("Removing file in MASH_HOME directory")
      for (file <- new File(MaShHome).listFiles) { file.delete }
    } else {}
  }

  def feature2String(f: (String, Double)): String = f match {
    case (str, num) => "%s=%.1f".format(str, num)
  }

  def learn(fact: String, parents: String, features: Set[(String, Double)], proof: Set[String]) = {
    val cmd = "! %s: %s; %s; %s".format(fact, parents, features.map(feature2String(_)).mkString(" "), proof.mkString(" "))
    // reporter.info("Running Mash command: " + cmd)
    // reporter.info("Result: " + run(cmd))
    run(cmd)
  }

  def relearn(fact: String, proof: Set[String]) = {
    val cmd = "p %s: %s".format(fact, proof.mkString(" "))
    // reporter.info("Result: " + run(cmd))
    run(cmd)
  }

  def str2Suggest(in: String): Set[(String, Double)] = {
    val sug = in.split(":")(1).trim()
    try {
      val rl = {
        for (f <- sug.split(" ")) yield {
          val newarr = f.split("=")
          (newarr(0), newarr(1).toDouble)
        }
      }
      rl.toSet
    } catch {
      case _: Throwable => Set()
    }
  }

  /*
   * Query suggestion from MaSh
   * 
   * Return a list of relevance facts sorted in decrease order
   */
  def query(name: String, parents: String, features: Set[(String, Double)], hints: Set[String] = Set[String]()) = {
    val cmd = {
      if (hints.isEmpty) "? %s: %s; %s".format(name, parents, features.map(feature2String(_)).mkString(" "))
      else "? %s: %s; %s; %s".format(name, parents, features.map(feature2String(_)).mkString(" "), hints.mkString(" "))
    }
    val output = run(cmd)
    // reporter.info("Result: " + output)

    str2Suggest(output)
  }

  /*
   * Execute command line and return output file content
   */
  def run(cmd: String): String = {
    // Create input file
    if (isOk) {
      try {
        val f: File = File.createTempFile("MaLe", ".cmd")
        val out = new PrintWriter(f, "UTF-8")
        out.print(cmd)
        out.close

        val run = "%s -q --saveModel --statistics --nb --modelFile %s --dictsFile %s --log %s --numberOfPredictions %d --inputFile %s  --predictions %s".format(
          command, MaShHome + "/mash_model.pickle", MaShHome + "/mash_dict.pickle", MaShHome + "/mash_log.txt", 2, f.getAbsolutePath, MaShHome + "/mash_sugg.txt")

        run.!! // reporter.info("Output: " + run.!!)
        f.deleteOnExit()
        Source.fromFile(MaShHome + "/mash_sugg.txt")(Codec.UTF8).mkString
      } catch {
        case _: Throwable => ""
      }
    } else { "" }
  }

}
