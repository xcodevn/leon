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
import scala.collection.mutable.MutableList

import leon.solvers.lemmafilter._
import leon.solvers.lemmafilter.MaLe._
import leon.solvers.rewriter._

import java.io._

/* Create a random list for cross-validation */
import scala.util.Random

object NewAnalysisPhase extends AnalysisPhaseClass {
  override val name = "New Analysis phase"
  override val description = "Leon Verification"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonValueOptionDef("functions", "--functions=f1:f2", "Limit verification to f1,f2,..."),
    LeonValueOptionDef("timeout",   "--timeout=T",       "Timeout after T seconds when trying to prove a verification condition."),
    LeonValueOptionDef("numvc",   "--numvc=n",           "Only checking n VCs for testing purpose"),
    LeonFlagOptionDef("training",   "--training",        "Train leon by using @depend"),
    LeonFlagOptionDef("cross-validation",   "--cross-validation",        "Doing cross-validate Naive-Bayes algorithm"),
    LeonFlagOptionDef("profiling",   "--profiling",      "Wait 10 sec for profiling"),
    LeonFlagOptionDef("create-testcase",   "--create-testcase",        "Write running options and output of verification into a file, and re-check in later running times ")
  )

  override def generateVerificationConditions(reporter: Reporter, program: Program, functionsToAnalyse: Set[String]): Map[FunDef, List[VerificationCondition]] = {
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

        allVCs += funDef -> funVCs.toList
      }
    }

    val notFound = functionsToAnalyse -- allVCs.keys.map(_.id.name)
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs
  }

  val egs = new MutableList[ (Expr, List[RewriteRule])] ()
  var allRules: List[RewriteRule] = null

  def checkVerificationConditions(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]], cap: Option[(Program, LeonContext)] = None) : VerificationReport = {
    val reporter = vctx.reporter
    val solvers  = vctx.solvers

    val interruptManager = vctx.context.interruptManager

    /* Create a new MePo filter here */
    val (ft, funLst) = cap match {
      case Some((p, c)) => (new TrivialFilter, p.definedFunctions)
      case _      => (new TrivialFilter, Seq())
    }

    val lst =  ( for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1); vcInfo <- vcs) yield { 
      (funDef, vcInfo)
    })

    val numVC = {
      var r: Int = lst.size
      vctx.context.options.foreach(op =>
          op match {
            case LeonValueOption("numvc", v) => r = v.toInt
            case _ =>
          })
      r
    }

    val simpleRewriter = new SimpleRewriter
    lst.take(numVC).foreach( p => {
      simpleRewriter.clearRules
      val (funDef, vcInfo) = p
      val t1 = System.nanoTime

      // val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
      reporter.debug(simplifyLets(vc))
      val svc = expandLets(vc)

      val ss_svc = cap match {
        case Some((program, ctx)) => {
          reporter.info("Simplify: \n" + svc + "\n======")
          // Push
          if(funDef.annotations.contains("induct")) {
            val iT = new ExtendedInductionTactic(reporter)
            for (r <- iT.generateInductiveHypothesisRewriteRules(funDef)) {
              simpleRewriter.addRewriteRule(r)
            }
          }
          simpleRewriter.setReporter(reporter)
          Rules.addDefaultRules(simpleRewriter)

          // Filtering is right here
          // In fact, we re-order fun in the best way we can, not filtering at all :|
          // println("Before " + funLst.map(_.id.toString))
          // val lst = Filtering.filter(Seq(ft), svc, funLst.filter(_ < funDef))
          val lst = funLst.filter(_ < funDef)
          // println("After  " + lst.map(_.id.toString))

          for (fun <- lst) {
            val rus = Rules.createFunctionRewriteRules(fun, program)
            for (ru <- rus) {
              val t1 = System.nanoTime
              simpleRewriter.addRewriteRule(ru)
            }
          }

          //println("Using simplifier")
          simpleRewriter.startTimer

          class SilentReporter extends DefaultReporter(Settings()) {
            override def output(msg: String) : Unit = { }
          }

          val ctx_wo_filter = LeonContext(new SilentReporter, ctx.interruptManager, ctx.settings, Seq(), Seq(), ctx.timers)
          val sf = new SolverFactory[Solver] {
            def getNewSolver() = { new UninterpretedZ3Solver(ctx_wo_filter, program) }
          }
          val simp_solver = SimpleSolverAPI(sf)

          def rec_simp(ex: Expr, count: Int = 5): Expr = { if (count == 0) println("Too much recusive")
            if (count == 0) ex else {
              val rl = cap match {
                case Some((program,ctx)) =>

                  val out = simpleRewriter.simplifyWithSolver(simp_solver)(ex, Seq())
                  if (out._2 == SIMP_SUCCESS())
                    out._1
                  else ex

                case _ => ex
              }
              if (rl.toString != ex.toString) {
                rec_simp(rl, count - 1)
              }
              else ex
            }
          }

          val ss_svc_temp1 = rec_simp(svc)
          val sopr = simpleRewriter.getSOPRules()
          egs.+= ((svc, sopr.toList))
          // val sopfd = sopr.map(x => x.name)
          // println("SOP Funtion " + sopfd)
          // out.write(sopfd.mkString(" ") + "\n")

          /* If simplied expr is too long (8 times longer than original expr) , back to original expr */
          val ss_svc_temp = if (ss_svc_temp1.toString.size > 8 * svc.toString.size) svc else ss_svc_temp1

          reporter.info("Our output \n============\n"  +ss_svc_temp.toString + "\n=============\n")
          ss_svc_temp
        }

        case _ => svc
      }

      if (ss_svc == BooleanLiteral(true)) {
        val t2 = System.nanoTime
        val dt = ((t2 - t1) / 1000000) / 1000.0
        reporter.info("==== VALID ====")
        vcInfo.hasValue = true
        vcInfo.value = Some(true)
        vcInfo.solvedWith = None // For now, None mean simplier 
        vcInfo.time = Some(dt)
        true
      } else {
      solvers.find(sf => {
        val s = sf.getNewSolver
        try {
          reporter.debug("Trying with solver: " + s.name)
          if (s.isInstanceOf[ExtendedFairZ3Solver]) {
            s.asInstanceOf[ExtendedFairZ3Solver].setCurrentFunction(funDef)
          }
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
    })

    allRules = simpleRewriter.getRules
    val report = new VerificationReport(vcs)
    report
  }

  def crossValidation(vctx: VerificationContext, vcs: Map[FunDef, List[VerificationCondition]], cap: Option[(Program, LeonContext)] = None) : VerificationReport = {
    val reporter = vctx.reporter
    val solvers  = vctx.solvers

    val interruptManager = vctx.context.interruptManager

    /* Create a new MePo filter here */
    val (ft, funLst) = cap match {
      case Some((p, c)) => (new TrivialFilter, p.definedFunctions)
      case _      => (new TrivialFilter, Seq())
    }

    val lst =  ( for((funDef, vcs) <- vcs.toSeq.sortWith((a,b) => a._1 < b._1); vcInfo <- vcs) yield { 
      (funDef, vcInfo)
    })

    val numVC = {
      var r: Int = lst.size
      vctx.context.options.foreach(op =>
          op match {
            case LeonValueOption("numvc", v) => r = v.toInt
            case _ =>
          })
      r
    }

    while (true) {
      val newlst = Random.shuffle(lst)       /* Create a random list */
      val checklst = newlst.take(numVC/10)   /* Only take 10 percent */
      val trainlst = newlst.drop(numVC/10)   /* The rest will be used for training purpose */
      val ml = new MaLeFilter()
      val exprs = checklst.map(x => expandLets(x._2.condition))

      /* Only training the rest of VCs */
      ml.training(egs.toList.filter { x => !exprs.contains(x._1) } , allRules)

      var c1 = 0
      var c2 = 0
      val s1 = System.nanoTime
      var st1 = 0.0
      var st2 = 0.0
      for (counter <- 0 until 20) {
        checklst.take(numVC).foreach( p => {
          val simpleRewriter = new SimpleRewriter
          val (funDef, vcInfo) = p
          val t1 = System.nanoTime

          // val funDef = vcInfo.funDef
          val vc = vcInfo.condition

          reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
          reporter.debug("Verification condition (" + vcInfo.kind + ") for ==== " + funDef.id + " ====")
          reporter.debug(simplifyLets(vc))
          val svc = expandLets(vc)

          val ss_svc = cap match {
            case Some((program, ctx)) => {
              reporter.info("Simplify: \n" + svc + "\n======")
              // Push
              if(funDef.annotations.contains("induct")) {
                val iT = new ExtendedInductionTactic(reporter)
                for (r <- iT.generateInductiveHypothesisRewriteRules(funDef)) {
                  simpleRewriter.addRewriteRule(r)
                }
              }
              simpleRewriter.setReporter(reporter)
              Rules.addDefaultRules(simpleRewriter)

              // Filtering is right here
              // In fact, we re-order fun in the best way we can, not filtering at all :|
              // println("Before " + funLst.map(_.id.toString))
              // val lst = Filtering.filter(Seq(ft), svc, funLst.filter(_ < funDef))
              val lst = funLst.filter(_ < funDef)
              // println("After  " + lst.map(_.id.toString))
              val fts = ml.getFeatureList(svc)

              for (fun <- lst) {
                val rus = Rules.createFunctionRewriteRules(fun, program)
                for (ru <- rus) {
                  if (counter % 2 == 0) {
                    // val t1 = System.nanoTime
                    val pr = ml.getPr(ru.name, fts)
                    // val del = System.nanoTime - t1
                    // println("Pr time " + del / 1000.0 / 1000)
                    if (pr > 1e-6) {
                      // println(" Using rule " + ru.name + " cause by pr " + pr)
                      simpleRewriter.addRewriteRule(ru)
                    }
                  } else {
                    simpleRewriter.addRewriteRule(ru)
                  }
                }
              }

              //println("Using simplifier")
              simpleRewriter.startTimer

              class SilentReporter extends DefaultReporter(Settings()) {
                override def output(msg: String) : Unit = { }
              }

              val ctx_wo_filter = LeonContext(new SilentReporter, ctx.interruptManager, ctx.settings, Seq(), Seq(), ctx.timers)
              val sf = new SolverFactory[Solver] {
                def getNewSolver() = { new UninterpretedZ3Solver(ctx_wo_filter, program) }
              }
              val simp_solver = SimpleSolverAPI(sf)

              def rec_simp(ex: Expr, count: Int = 5): Expr = { if (count == 0) println("Too much recusive")
                if (count == 0) ex else {
                  val rl = cap match {
                    case Some((program,ctx)) =>

                      val out = simpleRewriter.simplifyWithSolver(simp_solver)(ex, Seq())
                      if (out._2 == SIMP_SUCCESS())
                        out._1
                      else ex

                    case _ => ex
                  }
                  if (rl.toString != ex.toString) {
                    rec_simp(rl, count - 1)
                  }
                  else ex
                }
              }

              val ss_svc_temp1 = rec_simp(svc)
              // val sopr = simpleRewriter.getSOPRules()
              // egs.+= ((svc, sopr.toList))
              // val sopfd = sopr.map(x => x.name)
              // println("SOP Funtion " + sopfd)
              // out.write(sopfd.mkString(" ") + "\n")

              /* If simplied expr is too long (8 times longer than original expr) , back to original expr */
              val ss_svc_temp = if (ss_svc_temp1.toString.size > 8 * svc.toString.size) svc else ss_svc_temp1

              reporter.info("Our output \n============\n"  +ss_svc_temp.toString + "\n=============\n")
              ss_svc_temp
            }

            case _ => svc
          }

          if (ss_svc == BooleanLiteral(true)) {
            val t2 = System.nanoTime
            val dt = ((t2 - t1) / 1000000) / 1000.0
            reporter.info("==== VALID ====")
            vcInfo.hasValue = true
            vcInfo.value = Some(true)
            vcInfo.solvedWith = None // For now, None mean simplier 
            vcInfo.time = Some(dt)
            true
          } else {
          solvers.find(sf => {
            val s = sf.getNewSolver
            try {
              reporter.debug("Trying with solver: " + s.name)
              if (s.isInstanceOf[ExtendedFairZ3Solver]) {
                s.asInstanceOf[ExtendedFairZ3Solver].setCurrentFunction(funDef)
              }
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

          val d1 = System.nanoTime - s1
          if (counter % 2 == 0) st1 += d1 else st2 += d1
        })
      }

      println("st1: %f\nst2: %f\nspup: %f%%".format(st1, st2, (st2-st1)*100.0/st2))
      // Thread.sleep(3 * 1000)
    }


    // out.close()

    val report = new VerificationReport(vcs)
    report
  }

  def createTestcase(ctx: LeonContext, rp: VerificationReport) = {
    def infoLine(vc : VerificationCondition) : String = {
      "%-25s %-9s %9s %-8s %-10s".format(
        vc.funDef.id.toString, 
        vc.kind,
        vc.posInfo,
        vc.status,
        vc.tacticStr
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

  var doTraining: Boolean = false
  var doCrossValidation: Boolean = false
  var useMaLe: Boolean = false
  override def run(ctx: LeonContext)(program: Program) : VerificationReport = {
    var functionsToAnalyse   = Set[String]()
    var timeout: Option[Int] = None
    var create_testcase: Boolean = false

    for(opt <- ctx.options) opt match {
      case LeonValueOption("functions", ListValue(fs)) =>
        functionsToAnalyse = Set() ++ fs

      case v @ LeonValueOption("timeout", _) =>
        timeout = v.asInt(ctx)

      case v @ LeonValueOption("filter", "MaLe") => useMaLe = true

      case LeonFlagOption("training", v) => doTraining = v

      case LeonFlagOption("cross-validation", v) => doCrossValidation = v

      case LeonFlagOption("create-testcase", v) => create_testcase = v

      case LeonFlagOption("profiling", true) => { 
                                             println("Sleep 10 sec for profiling");
                                             try {
                                                   Thread.sleep(10000);
                                             } catch {
                                               case _ : Throwable => Thread.currentThread().interrupt();
                                             }
      }

                                            

      case _ =>
    }

    val reporter = ctx.reporter

    def isFlagTurnOn(f: String, ctx: LeonContext): Boolean = {
      for (op <- ctx.options) {
        op match {
          case LeonFlagOption(f1, v) if f == f1  => return v 
          case _ =>
        }
      }
      false
    }

    val isNotSimp = (isFlagTurnOn("codegen", ctx) || isFlagTurnOn("evalground", ctx))

    /*
    if (doTraining) {
      reporter.info("Training MaSh Filter from user guide...")
      val MaShFilter = new MaShFilter(ctx, program)
      MaShFilter.train
      MaShFilter.fairZ3.free()
    }
    */

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
      if (!isNotSimp) {
        checkVerificationConditions(vctx, vcs, Some(program, ctx))
        println("Sleep 10 seconds")
        // Thread.sleep(10 * 1000)
        crossValidation(vctx, vcs, Some(program, ctx))
      }
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
