package leon
package solvers.lemmafilter.mash

import java.io._
import scala.io._

/*
 * This is a low-level wrapper for MaSh
 */
object mash {
  import scala.sys.process._
  import leon._

  // create new reporter cause we don't use LeonContext
  val reporter = new DefaultReporter()

  var isOk = true

  def getEnv(name: String) = {
    try {
      sys.env(name)
    } catch {
      case _: Throwable =>
        reporter.error("Can NOT read " + name + " env variables")
        reporter.info("Disabled mash module")
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

  def unlearn = {
    reporter.info("MaSh unlearn")
    if (isOk) {
      reporter.info("Removing file in MASH_HOME directory")
      for (file <- new File(MaShHome).listFiles) { file.delete }
    } else {}
  }

  def feature2String(f: (String, Float)): String = f match {
    case (str, num) => "%s=%.1f".format(str, num)
  }

  def learn(fact: String, parents: String, features: Set[(String, Float)], proof: Set[String]) = {
    val cmd = "! %s: %s; %s; %s".format(fact, parents, features.map(feature2String(_)).mkString(" "), proof.mkString(" "))
    reporter.info("Running Mash command: " + cmd)
    reporter.info("Result: " + run(cmd))
  }

  def relearn(fact: String, proof: Set[String]) = {
    val cmd = "p %s: %s".format(fact, proof.mkString(" "))
    reporter.info("Result: " + run(cmd))
  }

  def str2Suggest(in: String): Set[(String, Float)] = {
    val sug = in.split(":")(1).trim()
    val rl = {
      for (f <- sug.split(" ")) yield {
       	val newarr = f.split("=")
    	(newarr(0), newarr(1).toFloat)
    }}
    rl.toSet
  } 
    
  
  def query(name: String, parents: String, features: Set[(String, Float)], hints: Set[String] = Set[String]()) = {
    val cmd = {
      if (hints.isEmpty) "? %s: %s; %s".format(name, parents, features.map(feature2String(_)).mkString(" "))
      else "? %s: %s; %s; %s".format(name, parents, features.map(feature2String(_)).mkString(" "), hints.mkString(" "))
    }
    val output = run(cmd)
    reporter.info("Result: " + output)
    
    str2Suggest(output)
  }

  def run(cmd: String): String = {
    // Create input file
    if (isOk) {
    try {
      val f: File = File.createTempFile("MaLe", ".cmd")
      f.deleteOnExit()
      val out = new PrintWriter(f, "UTF-8")
      out.print(cmd)
      out.close
      
      val run = "%s --modelFile %s --dictsFile %s --log %s --numberOfPredictions %d --inputFile %s  --predictions %s".format(
           MaShHome+"/mash_model.pickle", MaShHome + "/mash_dict.pickle", MaShHome + "/mash_log.txt", 5, f.getAbsolutePath, MaShHome + "/mash_sugg.txt")

      reporter.info("Output: " + run.!!)
      Source.fromFile(MaShHome + "/mash_sugg.txt")(Codec.UTF8).mkString
    } catch {
      case _: Throwable => ""
    }
    } else {""}
  }

}
