package leon
package solvers
package rewriter

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Extractors._
import collection.mutable.MutableList
import collection.mutable.{Map => MutableMap}

import leon.solvers.lemmafilter._
import scala.language.postfixOps


/**
 * The main purpose of this object is preaparing for calling filters and also combine filters result for
 * the best order of functions.
 */
object Filtering {
  private def createFunExpr(fun: FunDef): Expr = {
    /* We're trying to create an expression which contains all Pre-condition, Post-Condion and the implement */

    val truee = BooleanLiteral(true)
    val falsee = BooleanLiteral(false)
    val (res, post) = fun.postcondition.getOrElse( (FreshIdentifier("res"), falsee) )
    val imp = fun.implementation.getOrElse(truee)
    // return: pre -> post /\ res == imp
    return And(Implies(fun.precondition.getOrElse(truee), post), Equals(imp, Variable(res).setType(imp.getType)))
  }

  def filter(ft: Seq[Filter], expr: Expr, funLst: Seq[FunDef]): Seq[FunDef] = {
    /* We create a parameter for filters */
    val lemmas = funLst map {e => (e, createFunExpr(e)) } toMap 

    /**
     * Now, we only use one filter, 
     * Somehow, we can use list of filters by using a conbinator but it's something in future ;)
     */
    ft.head.filter(expr, lemmas, lemmas.size)
  }
}
