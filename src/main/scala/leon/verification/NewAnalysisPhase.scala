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

object NewAnalysisPhase extends AnalysisPhaseClass {
  override val name = "New Analysis phase"
  override val description = "Leon Verification"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition."),
    LeonFlagOptionDef("training",   "--training",        "Train leon by using @depend"),
    LeonFlagOptionDef("create-testcase",   "--create-testcase",        "Write running options and output of verification into a file, and re-check in later running times ")
  )

  override def generateVerificationConditions(reporter: Reporter, program: Program, functionsToAnalyse: Set[String]): Map[FunDef, List[VerificationCondition]] = {
    val defaultTactic = new DefaultTactic(reporter)
    defaultTactic.setProgram(program)
    val inductionTactic = new ExtendedInductionTactic(reporter)
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

        allVCs += funDef -> funVCs.toList
      }
    }

    val notFound = functionsToAnalyse -- allVCs.keys.map(_.id.name)
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs
  }

  def checkVerificationConditions(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]], cap: Option[(Program, LeonContext)] = None) : VerificationReport = {
    val reporter = vctx.reporter
    val solvers  = vctx.solvers

    val interruptManager = vctx.context.interruptManager


    /* Create a new MePo filter here */
    val (ft, funLst) = cap match {
      case Some((p, c)) => (new TrivialFilter, p.definedFunctions)
      case _      => (new TrivialFilter, Seq())
    }

    for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1)) {
      funDef.isReach = true
      for (vcInfo <- vcs if !interruptManager.isInterrupted()) {
        val t1 = System.nanoTime

        val funDef = vcInfo.funDef
        val vc = vcInfo.condition

        reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
        reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
        reporter.debug(simplifyLets(vc))
        val svc = expandLets(vc)
        
        def rec_simp(ex: Expr, count: Int = 5): Expr = {
          if (count == 0) println("Too much recusive")
          if (count == 0) ex else {
            val rl = cap match {
              case Some((program,ctx)) =>
                val sf1 = SolverFactory( () => new UninterpretedZ3Solver(ctx, program))
                val sf  = new TimeoutSolverFactory(sf1, 10L)
                val out = SimpleRewriter.simplify(sf)(ex, Seq())
                out._1

              case _ => ex
            }
            if (rl.toString != ex.toString) {
              rec_simp(rl, count - 1)
            }
            else ex
          }
        }

        val ss_svc = cap match {
          case Some((program, ctx)) => {
            reporter.info("Simplify: \n" + svc + "\n======")
            // Push
            SimpleRewriter.push()

            // Filtering is right here
            // In fact, we re-order fun in the best way we can, not filtering at all :|
            // println("Before " + funLst.map(_.id.toString))
            // val lst = Filtering.filter(Seq(ft), svc, funLst.filter(e => e.isReach && e != funDef))

            /* We don't filter, because this is original implementation */
            val lst= funLst.filter(e => e.isReach && e != funDef)
            // println("After  " + lst.map(_.id.toString))

            for (fun <- lst) {
              val rus = Rules.createFunctionRewriteRules(fun, program)
              for (ru <- rus) SimpleRewriter.addRewriteRule(ru)
            }

            SimpleRewriter.startTimer

            val ss_svc_temp1 = rec_simp(svc)
            val ss_svc_temp = if (ss_svc_temp1.toString.size > 8 * svc.toString.size) svc else ss_svc_temp1
            SimpleRewriter.pop() // Reset status as before filtering

            reporter.info("Our output \n============\n"  +ss_svc_temp.toString + "\n=============\n")
            ss_svc_temp
          }

          case _ => svc
        }

        // try all solvers until one returns a meaningful answer
        solvers.find(sf => {
          val s = sf.getNewSolver
          try {
            reporter.debug("Trying with solver: " + s.name)
            s.assertCnstr(Not(ss_svc))

            val satResult = s.check
            val counterexample: Map[Identifier, Expr] = if (satResult == Some(true)) s.getModel else Map()
            val solverResult = satResult.map(!_)

            val t2 = System.nanoTime
            val dt = ((t2 - t1) / 1000000) / 1000.0

            solverResult match {
              case _ if interruptManager.isInterrupted() =>
                reporter.info("=== CANCELLED ===")
                vcInfo.time = Some(dt)
                vcInfo.goal = Some(ss_svc)
                false

              case None =>
                vcInfo.time = Some(dt)
                vcInfo.goal = Some(ss_svc)
                false

              case Some(true) =>
                reporter.info("==== VALID ====")

                vcInfo.hasValue = true
                vcInfo.value = Some(true)
                vcInfo.solvedWith = Some(s)
                vcInfo.time = Some(dt)
                true

              case Some(false) =>
                reporter.error("Found counter-example : ")
                reporter.error(counterexample.toSeq.sortBy(_._1.name).map(p => p._1 + " -> " + p._2).mkString("\n"))
                reporter.error("==== INVALID ====")
                vcInfo.hasValue = true
                vcInfo.value = Some(false)
                vcInfo.solvedWith = Some(s)
                vcInfo.counterExample = Some(counterexample)
                vcInfo.time = Some(dt)
                true
            }
          } finally {
            s.free()
          }}) match {
            case None => {
              vcInfo.hasValue = true
              reporter.warning("==== UNKNOWN ====")
            }
            case _ =>
          }
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

    def isFlagTurnOn(f: String, ctx: LeonContext): Boolean = {
      for (op <- ctx.options) {
        op match {
          case LeonFlagOption(f, v) => return v
          case _ =>
        }
      }
      false
    }

    class SilentReporter extends DefaultReporter(Settings()) {
      override def output(msg: String) : Unit = { }
    }

    SimpleRewriter.clearRules
    SimpleRewriter.setReporter(reporter)
    val ctx_wo_filter = LeonContext(new SilentReporter, ctx.interruptManager, ctx.settings, Seq(), Seq(), ctx.timers)
    val isNotSimp = (isFlagTurnOn("codegen", ctx) || isFlagTurnOn("feelinglucky", ctx) || isFlagTurnOn("evalground", ctx))
    if  (!isNotSimp) {

      /*
      for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if !funDef.hasPostcondition) {
        // println(funDef)
        val rus = Rules.createFunctionRewriteRules(funDef, program)
        for (ru <- rus) SimpleRewriter.addRewriteRule(ru)
      }
      */
      Rules.addDefaultRules(SimpleRewriter)
    }

    if (doTraining) {
      reporter.info("Training MaSh Filter from user guide...")
      val MaShFilter = new MaShFilter(ctx, program)
      MaShFilter.train
      MaShFilter.fairZ3.free()
    }

    val baseFactories = Seq(
      SolverFactory(() => new ExtendedFairZ3Solver(ctx, program))
    )

    val solverFactories = timeout match {
      case Some(sec) =>
        baseFactories.map { sf =>
          new TimeoutSolverFactory(sf, sec*1000L)
        }
      case None =>
        baseFactories
    }

    val vctx = VerificationContext(ctx, solverFactories, reporter)

    val report = {
      reporter.debug("Running verification condition generation...")
      val vcs = generateVerificationConditions(reporter, program, functionsToAnalyse)
      if (!isNotSimp)
        checkVerificationConditions(vctx, vcs, Some(program, ctx))
      else
        checkVerificationConditions(vctx, vcs, None)
    }

    if (create_testcase) {
      reporter.info("Writing down options and output...")
      createTestcase(ctx, report)
    }
    report
  }
}
