package leon
package solvers
package lemmafilter

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

class TrivialFilter extends Filter {
  val name = "Trivial Filter"
  val description = "This filter does not do anything just return original list of lemmas!"

  def filter(conjecture: Expr, m: Map[FunDef, Expr]): Seq[FunDef] = m.keySet.toSeq.filter(f => f.annotations.contains("lemma"))
}
