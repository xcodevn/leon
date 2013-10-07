/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test
package solvers.lemmafilter

import leon.verification.{NewAnalysisPhase,VerificationReport,VerificationCondition}

import java.io.File
import scala.io._

class NewTestFramework extends LeonTestSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }
  private case class Output(report : VerificationReport, reporter : Reporter)

  private def mkPipeline : Pipeline[List[String],VerificationReport] =
    leon.plugin.ExtractionPhase andThen leon.utils.SubtypingPhase andThen leon.verification.NewAnalysisPhase

  private def mkTest(file : File, leonOptions : Seq[LeonOption], forError: Boolean)(block: Output=>Unit) = {
    val fullName = file.getPath()
    val start = fullName.indexOf("regression")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("%3d: %s %s".format(nextInt(), displayName, leonOptions.mkString(" "))) {
      assert(file.exists && file.isFile && file.canRead,
             "Benchmark %s is not a readable file".format(displayName))

      val ctx = testContext.copy(
        options = leonOptions.toList,
        files   = List(file)
      )

      val pipeline = mkPipeline

      if(forError) {
        intercept[LeonFatalError]{
          pipeline.run(ctx)(file.getPath :: Nil)
        }
      } else {

        val report = pipeline.run(ctx)(file.getPath :: Nil)

        block(Output(report, ctx.reporter))
      }
    }
  }

  private def forEachFileIn(cat : String, forError: Boolean = false) {
    val fs = filesInResourceDir(
      "regression/verification/lemma-filter/" + cat,
      _.endsWith(".scala"))

    def parseOpt(str: String): List[LeonOption] = {
      val lst = for(opt <- str.split(" ")) yield {
        val lst = opt.split(":")
        if (lst(1) == "true") LeonFlagOption(lst(0), true)
        else if (lst(1) == "false") LeonFlagOption(lst(0), false)
        else LeonValueOption(lst(0), lst(1))
      }
      lst.toList
    }

    for(f <- fs.toSeq.sorted) {
      val tcf = new File(f.getParentFile, f.getName + ".testcase")
      val cont = Source.fromFile(tcf)(Codec.UTF8).mkString
      val lst = cont.split("\n")
      mkTest(f, parseOpt(lst(0)), forError)(output => {
        val Output(report, reporter) = output
        def infoLine(vc : VerificationCondition) : String = {
          "%-25s %-9s %9s %-8s %-10s %-7s".format(
            vc.funDef.id.toString, 
            vc.kind,
            vc.posInfo,
            vc.status,
            vc.tacticStr,
            vc.solverStr
            )
        }
        val fmt = report.conditions.map(infoLine).toList
        val llst = lst.toList.tail
        assert(llst == fmt, "Current output: \n"+ fmt.mkString("\n") + "\nIt should be \n" + llst.mkString("\n"))
      })
    }
  }
  
  forEachFileIn("rerun")
}
