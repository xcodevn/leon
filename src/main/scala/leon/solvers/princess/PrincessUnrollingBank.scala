package leon
package solvers.princess

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }
import leon.purescala.Definitions._
import leon.purescala.Trees._
import ap.parser.IExpression
import ap.parser.IFormula

class PrincessUnrollingBank(val solver: PrincessSolver, val reporter: Reporter) {
  // Keep which function invocation is guarded by which guard,
  // also specify the generation of the blocker.

  private var blockersInfoStack: List[MutableMap[IFormula, (Int, Int, IFormula, Set[PrincessFunctionInvocation])]] = List(MutableMap())

  def blockersInfo = blockersInfoStack.head

  // Note that this computes cumulated sets.
  private var unlockedStack: List[MutableSet[IFormula]] = List(MutableSet())
  def unlockedSet: MutableSet[IFormula] = unlockedStack.head
  def wasUnlocked(id: IFormula): Boolean = unlockedStack.head(id)

  def push() {
    blockersInfoStack = (MutableMap() ++ blockersInfo) :: blockersInfoStack
    unlockedStack = (MutableSet() ++ unlockedStack.head) :: unlockedStack
  }

  def pop(lvl: Int) {
    blockersInfoStack = blockersInfoStack.drop(lvl)
    unlockedStack = unlockedStack.drop(lvl)
  }

  def currentPrincessBlockers = blockersInfo.map(_._2._3)

  def dumpBlockers = {
    blockersInfo.groupBy(_._2._1).toSeq.sortBy(_._1).foreach {
      case (gen, entries) =>
        reporter.info("--- " + gen)

        for (((bast), (gen, origGen, ast, fis)) <- entries) {
          reporter.info(".     " + bast + " ~> " + fis.map(_.funDef.id))
        }
    }
  }

  def canUnroll = !blockersInfo.isEmpty

  def getPrincessBlockersToUnlock: Seq[IExpression] = {
    if (!blockersInfo.isEmpty) {
      val minGeneration = blockersInfo.values.map(_._1).min

      blockersInfo.filter(_._2._1 == minGeneration).toSeq.map(_._1)
    } else {
      Seq()
    }
  }

  private def registerBlocker(gen: Int, id: IFormula, fis: Set[PrincessFunctionInvocation]) {
    val not_id = !id.asInstanceOf[IFormula]
    blockersInfo.get(id) match {
      case Some((exGen, origGen, _, exFis)) =>
        // PS: when recycling `b`s, this assertion becomes dangerous.
        // It's better to simply take the min of the generations.
        // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

        val minGen = gen max exGen

        blockersInfo(id) = ((minGen, origGen, not_id, fis ++ exFis))
      case None =>
        blockersInfo(id) = ((gen, gen, not_id, fis))
    }
  }

  //DONE
  def scanForNewTemplates(expr: Expr): Seq[IExpression] = {
    // OK, now this is subtle. This `getTemplate` will return
    // a template for a "fake" function. Now, this template will
    // define an activating boolean...
    val template = PrincessFunctionTemplate.getTemplate(solver, expr)

    val princessArgs = for (vd <- template.funDef.args) yield {
      solver.lookupOrCreate(vd.id)
    }

    // ...now this template defines clauses that are all guarded
    // by that activating boolean. If that activating boolean is 
    // undefined (or false) these clauses have no effect...
    val (newClauses, newBlocks) =
      template.instantiate(template.princessActivatingBool, princessArgs)

    for ((i, fis) <- newBlocks) {
      registerBlocker(nextGeneration(0), i.asInstanceOf[IFormula], fis)
    }

    // ...so we must force it to true!
    template.princessActivatingBool +: newClauses
  }

  def nextGeneration(gen: Int) = gen + 3

  def decreaseAllGenerations() = {
    for ((block, (gen, origGen, ast, finvs)) <- blockersInfo) {
      // We also decrease the original generation here
      blockersInfo(block) = (math.max(1, gen - 1), math.max(1, origGen - 1), ast, finvs)
    }
  }

  def promoteBlocker(b: IFormula) = {
    if (blockersInfo contains b) {
      val (gen, origGen, ast, finvs) = blockersInfo(b)
      blockersInfo(b) = (1, origGen, ast, finvs)
    }
  }

  def unlock(id: IFormula): Seq[IExpression] = {
    assert(blockersInfo contains id)

    if (unlockedSet(id)) return Seq.empty

    val (gen, origGen, _, fis) = blockersInfo(id)

    blockersInfo -= id
    val twice = wasUnlocked(id)

    var newClauses: Seq[IExpression] = Seq.empty

    var reintroducedSelf: Boolean = false
    
    for (fi <- fis) {
      val template = PrincessFunctionTemplate.getTemplate(solver, fi.funDef)
      val (newExprs, newBlocks) = template.instantiate(id, fi.args)

      for ((i, fis2) <- newBlocks) {
        registerBlocker(nextGeneration(gen), i.asInstanceOf[IFormula], fis2)
        if (i == id) {
          reintroducedSelf = true
        }
      }

      newClauses ++= newExprs
    }

    if (!reintroducedSelf) {
      unlockedSet += id
    }

    newClauses
  }

}

