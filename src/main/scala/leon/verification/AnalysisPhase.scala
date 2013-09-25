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
import leon.solvers.rewriter._

import java.io._

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  implicit val debugSection = DebugSectionVerification

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition."),
    LeonFlagOptionDef("training",   "--training",        "Train leon by using @depend"),
    LeonFlagOptionDef("create-testcase",   "--create-testcase",        "Write running options and output of verification into a file, and re-check in later running times ")
  )

  def generateVerificationConditions(reporter: Reporter, program: Program, functionsToAnalyse: Set[String]): Map[FunDef, List[VerificationCondition]] = {
    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(program)
    val inductionTactic = new InductionTactic(reporter)
    inductionTactic.setProgram(program)

    var allVCs = Map[FunDef, List[VerificationCondition]]()

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (functionsToAnalyse.isEmpty || functionsToAnalyse.contains(funDef.id.name))) {

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        val funVCs = tactic.generatePreconditions(funDef) ++
                     tactic.generatePatternMatchingExhaustivenessChecks(funDef) ++
                     tactic.generatePostconditions(funDef) ++
                     tactic.generateMiscCorrectnessConditions(funDef) ++
                     tactic.generateArrayAccessChecks(funDef)

                     allVCs += funDef -> funVCs.toList.sortWith( (fvc1, fvc2) => fvc1.condition.toString < fvc2.condition.toString)
      }
    }

    val notFound = functionsToAnalyse -- allVCs.keys.map(_.id.name)
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs
  }

  def checkVerificationConditions(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]], rwSolver: SolverFactory[Solver]) : VerificationReport = {
    val reporter = vctx.reporter
    val solvers  = vctx.solvers

    val interruptManager = vctx.context.interruptManager

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1); vcInfo <- vcs if !interruptManager.isInterrupted()) {
      val funDef = vcInfo.funDef
      funDef.isReach = true
      val vc = vcInfo.condition

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.debug(simplifyLets(vc))
      val svc = simplifyLets(vc)

      def rec_simp(ex: Expr): Expr = {
        val out = SimpleRewriter.simplify(rwSolver)(ex, Seq())
        return out._1
        if (out._1 != ex) rec_simp(out._1) else ex
      }

      println("Simplify: \n" + svc + "\n======")
      val ss_svc = rec_simp(svc)
      println("Our output \n============\n"  +ss_svc.toString + "\n=============\n")

      // try all solvers until one returns a meaningful answer
      solvers.find(se => {
        reporter.debug("Trying with solver: " + se.name)
        val t1 = System.nanoTime
        val (satResult, counterexample) = SimpleSolverAPI(se).solveSAT(Not(ss_svc))
        val solverResult = satResult.map(!_)

        val t2 = System.nanoTime
        val dt = ((t2 - t1) / 1000000) / 1000.0

        solverResult match {
          case _ if interruptManager.isInterrupted() =>
            reporter.info("=== CANCELLED ===")
            vcInfo.time = Some(dt)
            false

          case None =>
            vcInfo.time = Some(dt)
            false

          case Some(true) =>
            reporter.info("==== VALID ====")

            vcInfo.hasValue = true
            vcInfo.value = Some(true)
            vcInfo.solvedWith = Some(se)
            vcInfo.time = Some(dt)
            true

          case Some(false) =>
            reporter.error("Found counter-example : ")
            reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
            reporter.error("==== INVALID ====")
            vcInfo.hasValue = true
            vcInfo.value = Some(false)
            vcInfo.solvedWith = Some(se)
            vcInfo.counterExample = Some(counterexample)
            vcInfo.time = Some(dt)
            true
        }
      }) match {
        case None => {
          vcInfo.hasValue = true
          reporter.warning("==== UNKNOWN ====")
        }
        case _ =>
      }
    }

    val report = new VerificationReport(vcs)
    report
  }

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

  

  def run(ctx: LeonContext)(program: Program) : VerificationReport = {
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

    val fairZ3 = new FairZ3SolverFactory(ctx, program)

    class SilentReporter extends DefaultReporter(Settings()) {
      override def output(msg: String) : Unit = { }
    }

    val ctx_wo_filter = LeonContext(new SilentReporter, ctx.interruptManager, ctx.settings, Seq(), Seq(), ctx.timers)
    val rwSolver = new FairZ3SolverFactory(ctx_wo_filter, program)

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2)) {
      println(funDef.id)
      val rus = Rules.createFunctionRewriteRules(funDef, program)
      for (ru <- rus) SimpleRewriter.addRewriteRule(ru)
    }
    Rules.addDefaultRules(SimpleRewriter)

    SimpleRewriter.pp_rules

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
      checkVerificationConditions(vctx, vcs, rwSolver)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
      VerificationReport.emptyReport
    }

    solvers.foreach(_.free())
    rwSolver.free()

    if (create_testcase) {
      reporter.info("Writing down options and output...")
      createTestcase(ctx, report)
    }
    report
  }
}
