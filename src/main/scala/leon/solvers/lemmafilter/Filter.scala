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
trait Filter {
  // This class is a model for other filters
  //
  // For each filter, we need a entry function to input list of lemma (only once time) and
  // other function for filter operation
  //
  // This function will return a subset of lemmas which are really necessary for proof of `conjecture`
  def filter(conjecture: Expr, m: Map[FunDef, Expr], num_lemmas: Int): Seq[FunDef]
}

