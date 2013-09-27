
package leon.solvers.lemmafilter

import leon.utils._
import z3.scala._

import leon.solvers.Solver

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.Extractors._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon._
import leon.solvers.z3._
import leon.evaluators._

import leon.termination._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import scala.collection.mutable.MutableList



object LemmaEngine {
  var ctx : Option[LeonContext] = None
  var prog : Option[Program] = None
  var lemmaFlag: Boolean = false
  var filterOption: String = "NOT USED"
  var numLemmasOption: Int = 2
  var addLemmaYet: Boolean = false
  var solver: Option[Z3Solver] = None
  var z3: Option[Z3Context] = None
  var fairSolver: Option[AbstractZ3Solver] = None
  var reporter: Option[Reporter] = None

  def setup(z3: Z3Context, ctx: LeonContext, prog: Program) = {
    this.ctx = Some(ctx)
    this.prog = Some(prog)
    this.z3 = Some(z3)

    for(opt <- ctx.options) opt match {
      case LeonFlagOption("lemmas", v)             => lemmaFlag           = v
      case LeonValueOption("filter", v)            => { filterOption = v; if (v=="MaSh" || v == "MePo") lemmaFlag = true }
      case LeonValueOption("num-lemmas", v)        => numLemmasOption = v.toInt
        
      case _ =>
    }
  }

  def setZ3Solver(solver: Z3Solver) = {
    this.solver = Some(solver)
  }

  def setFairSolver(solver: AbstractZ3Solver) = {
    this.fairSolver = Some(solver)
  }


  def doFilter(expression: Expr) = {
    /* Only use filter in the first time of calling this function */
    (z3, ctx, prog, solver, reporter, fairSolver) match {
      case (Some(z3), Some(context), Some(program), Some(solver), Some(reporter), Some(fairSolver)) => {
        if(lemmaFlag && ! addLemmaYet) {
          addLemmaYet = true
          //lemmaZ3ASTs.clear()
          // val lemmaZ3ASTs: MutableList[Z3AST] = new MutableList[Z3AST]()
          filterOption match {
            case "MaSh" =>
              val MaShfilter = new MaShFilter(context, program)
              val curFun = program.definedFunctions.filter(f=>f.isReach).sortWith( (fd1,fd2) => fd1 < fd2 ).reverse.head
              val funs = curFun +: program.definedFunctions.filter(f => f < curFun)
              if (curFun.annotations.contains("depend")) {
                curFun.dependencies match { case Some(deps) => Z3Lemmas.prepareLemmas(z3, solver, fairSolver, funs.filter(f => deps.contains(f.id.name.toString))); case _ => }
              } else {
                val m = funs.tail.filter(f => f.annotations.contains("lemma")).map( f => (f, Error(":-)"))).toMap
                if (m.size > 0)
                  Z3Lemmas.prepareLemmas(z3, solver, fairSolver, MaShfilter.filter(expression, m, numLemmasOption) )
              }
              MaShfilter.fairZ3.free() // go away z3 ;)

            case "MePo" =>
              val MePofilter = new MePoFilter(context, program)
              val curFun = program.definedFunctions.filter(f=>f.isReach).sortWith( (fd1,fd2) => fd1 < fd2 ).reverse.head
              val funs = curFun +: program.definedFunctions.filter(f => f < curFun)
              if (curFun.annotations.contains("depend")) {
                curFun.dependencies match { case Some(deps) => Z3Lemmas.prepareLemmas(z3, solver, fairSolver, funs.filter(f => deps.contains(f.id.name.toString))); case _ => }
              } else {
                val m = funs.tail.filter(f => f.annotations.contains("lemma")).map( f => (f, MePofilter.genVC(f))).toMap
                if (m.size > 0) {
                  val res = MePofilter.filter(expression, m, numLemmasOption)
                  Z3Lemmas.prepareLemmas(z3, solver, fairSolver, res)
                }
              }
              MePofilter.fairZ3.free() // I don't need you anymore

            case _ =>
              Z3Lemmas.prepareLemmas(z3, solver, fairSolver, program.definedFunctions.filter(f=> f.annotations.contains("lemma"))) /* As before I come here ;) */
          }
        }
      }

      case _ =>
    }
  }


}
