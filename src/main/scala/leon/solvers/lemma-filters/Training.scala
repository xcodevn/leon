package leon
package solvers.z3

import z3.scala._

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._
import leon.solvers.lemmafilter.mash._

trait Z3Training {
  self : AbstractZ3Solver =>

  def train = {
    import scala.sys.process._
    reporter.warning("FIXME: implement train() as a high-level wrapper for MaSh python source code")

    /*
     * We use mash API (learn, unlearn, ...) for this training process
     *
     */
    mash.unlearn

    /*

    for(funDef <- program.definedFunctions if funDef.annotations.contains("lemma")) {
      val fname = funDef.id.name

      if(!(funDef.returnType == BooleanType)) {
        reporter.error("Function [%s] is marked as a lemma but is not a predicate.".format(fname))
      } else {
        funDef.postcondition match {
          case None =>
            reporter.error("Function [%s] is marked as a lemma but does not have a postcondition.".format(fname))
          case Some(post) =>
              reporter.warning("FIXME: Now we don't check if the lemmas return a boolean value or not!")
              funDef.implementation match {
                  case None =>
                    reporter.error("Function [%s] is marked as a lemma but does not have a body.".format(fname))
                  case Some(imple) =>
                    // So this looks like a good lemma :D
                    reporter.info("Yeepee! [%s] is a nice lemma!".format(fname))

        val lemmaBody : Expr = funDef.precondition.map { pre =>
          Implies(pre, imple)
        } getOrElse {
          imple
        }
        
        val fArgs : Seq[Variable] = funDef.args.map(_.toVariable)
        val argSorts : Seq[Z3Sort] = fArgs.map(v => typeToSort(v.getType))
        val bounds : Seq[Z3AST] = argSorts.zipWithIndex.map { case (s, i) => z3.mkBound(i, s) }
        val namedBounds : Seq[(Z3Symbol,Z3Sort)] = argSorts.map(a => (z3.mkFreshStringSymbol("qx"), a))
        val initialMap : Map[Identifier,Z3AST] = fArgs.map(_.id).zip(bounds).toMap 

        // FIXME : that ".get" is bolder that we want it to be.
        // Also: Apply matchToIfThenElse and let-expansion
        val quantBody : Z3AST = toZ3Formula(matchToIfThenElse(lemmaBody), initialMap).get

        val varSet : Set[Identifier] = fArgs.map(_.id).toSet
        val preMps : Set[Set[Expr]] = funDef.precondition match {
          case Some(precond) =>
            extractMultiPatterns(matchToIfThenElse(precond), varSet)
          case None =>
            Set.empty
        }

        val multiPatterns : Set[Set[Expr]] = if(!preMps.isEmpty) {
          preMps
        } else {
          extractMultiPatterns(matchToIfThenElse(lemmaBody), varSet)
        }

        def flatten(xs: List[Any]): List[Any] = xs match {
          case Nil => Nil
          case (head: List[_]) :: tail => flatten(head) ++ flatten(tail)
          case head :: tail => head :: flatten(tail)
        }

        reporter.info(" *** Multipatterns for lemma [%s].".format(fname))
        val lst = for(mp <- multiPatterns) yield {
          reporter.info("--- ")
          reporter.info("--- " + mp.mkString("[", "; ", "]"))
      
          mp.toSeq.map(c => toZ3Formula(c, initialMap).get)
        }


        reporter.info(lst.toSeq)

        val z3MultiPatterns = z3.mkPattern(lst.toSeq.flatten : _*)

        val axiom : Z3AST = z3.mkForAll(0, Seq(z3MultiPatterns), namedBounds, quantBody)

        reporter.info("Look ! I made an axiom !")
        reporter.info(axiom.toString)
        solver.assertCnstr(axiom)
      }}}
    }
    */
  }

}
