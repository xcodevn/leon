/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import solvers._
import solvers.z3._

import scala.collection.mutable.{Set => MutableSet}

import leon.solvers.lemmafilter._

import java.io._

object NewAnalysisPhase extends AnalysisPhaseClass {
  override val name = "New Analysis phase"
  override val description = "Leon Verification"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition."),
    LeonFlagOptionDef("training",   "--training",        "Train leon by using @depend"),
    LeonFlagOptionDef("create-testcase",   "--create-testcase",        "Write running options and output of verification into a file, and re-check in later running times ")
  )

  def createTestcase(ctx: LeonContext, rp: VerificationReport) = {
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
    val opt = ctx.options.foldLeft ( List[String]() ) ( ( lst, op) => {
      val s = Set[String]("filter", "training", "timeout", "num-lemmas", "functions")
      op match {
        case LeonFlagOption(key, va) => if (s.contains(key)) "%s:%s".format(key, va.toString) :: lst else lst

        case LeonValueOption(key, va) => if (s.contains(key)) "%s:%s".format(key, va) :: lst else lst
      }
    })

    val fn = ctx.files.head.getName
    val pa = ctx.files.head.getParentFile
    val f = new File(pa, fn + ".testcase")
    val out = new PrintWriter(f, "UTF-8")
    val txtrp = rp.conditions.map(infoLine).mkString("\n")
    out.println(opt.mkString(" "))
    out.println(txtrp)
    out.close
  }

  

  override def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    var functionsToAnalyse   = Set[String]()
    var timeout: Option[Int] = None
    var doTraining: Boolean = false
    var create_testcase: Boolean = false

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case LeonFlagOption("training", v) => doTraining = v

      case LeonFlagOption("create-testcase", v) => create_testcase = v

      case _ =>
    }

    val reporter = ctx.reporter

    val fairZ3 = new ExtendedFairZ3Solver(ctx, program)

    if (doTraining) {
      reporter.info("Training MaSh Filter from user guide...")
      val MaShFilter = new MaShFilter(ctx, program)
      MaShFilter.train
      MaShFilter.fairZ3.free()
    }

    val baseSolvers : Seq[SolverFactory[Solver]] = fairZ3 :: Nil

    val solvers: Seq[SolverFactory[Solver]] = timeout match {
      case Some(t) =>
        baseSolvers.map(_.withTimeout(100L*t))

      case None =>
        baseSolvers
    }

    val vctx = VerificationContext(ctx, solvers, reporter)

    val report = if(solvers.size >= 1) {
      reporter.debug("Running verification condition generation...")
      val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
      checkVerificationConditions(vctx, vcs)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    solvers.foreach(_.free())

    if (create_testcase) {
      reporter.info("Writing down options and output...")
      createTestcase(ctx, report)
    }
    report
  }
}
