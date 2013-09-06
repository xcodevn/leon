// A lemma filter for provers

package leon
package solvers
package lemmafilter

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._

//
// This class is built base on Solver.scala
// We need a stable API for filters
//
abstract class Filter(val context : LeonContext) {
  // This class is a model for other filters
  //
  // For each filter, we need a entry function to input list of lemma (only once time) and
  // other function for filter operation
  //

  // I don't know if this function is necessary
  def setProgram(program: Program) : Unit = {}

  // Don't know what Expr and Seq type really is but ... 
  // This function will return a subset of lemmas which are really necessary for proof of `conjecture`
  def filter(conjecture: Expr): Seq[Expr]

  // Set list of lemmas for the first time
  // (May I put it became a contructor? )
  def setListOfLemmas(lemmas: Seq[Expr]): Unit
}

