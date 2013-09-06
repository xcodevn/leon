package leon
package solvers
package lemmafilter

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

class TrivialFilter(context: LeonContext) extends Filter(context) {
  val name = "trivial filter"
  val description = "This filter does not do anything just return original list of lemmas!"

  private var listOfLemmas: Seq[Expr] = Nil

  def filter(conjecture: Expr): Seq[Expr] = listOfLemmas

  def setListOfLemmas(lst: Seq[Expr]): Unit = { listOfLemmas = lst }
}
