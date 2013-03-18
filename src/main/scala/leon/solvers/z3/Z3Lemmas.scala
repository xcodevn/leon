package leon
package solvers.z3

import z3.scala._

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._

trait Z3Lemmas {
  self : AbstractZ3Solver =>

  private lazy val lemmaPost : Expr = ResultVariable().setType(BooleanType)

  def prepareLemmas(solver : Z3Solver) : Unit = {
    for(funDef <- program.definedFunctions if funDef.annotations.contains("lemma")) {
      val fname = funDef.id.name

      if(!(funDef.returnType == BooleanType)) {
        reporter.error("Function [%s] is marked as a lemma but is not a predicate.".format(fname))
      } else if(!funDef.hasPostcondition) {
        reporter.error("Function [%s] is marked as a lemma but does not have a postcondition.".format(fname))
      } else if(funDef.getPostcondition != lemmaPost) {
        reporter.error("Invalid postcondition for lemma [%s].".format(fname))
      } else if(funDef.hasPrecondition) {
        reporter.error("Lemma [%s] should not have a precondition. Use an implication in the body instead.".format(fname))
      } else {
        // So this looks like a good lemma :D
        reporter.info("Yeepee! [%s] is a nice lemma!".format(fname))
        
        val fArgs : Seq[Variable] = funDef.args.map(_.toVariable)
        val argSorts : Seq[Z3Sort] = fArgs.map(v => typeToSort(v.getType))
        val bounds : Seq[Z3AST] = argSorts.zipWithIndex.map { case (s, i) => z3.mkBound(i, s) }
        val namedBounds : Seq[(Z3Symbol,Z3Sort)] = argSorts.map(a => (z3.mkFreshStringSymbol("qx"), a))
        val initialMap : Map[Identifier,Z3AST] = fArgs.map(_.id).zip(bounds).toMap 

        // FIXME : that ".get" is bolder that we want it to be.
        val quantBody : Z3AST = toZ3Formula(funDef.getImplementation, initialMap).get

        // I know, they're really function invocations, but who cares.
        val calls : Seq[Expr] = functionCallsOf(funDef.getImplementation).toSeq

        val patterns : Seq[Z3Pattern] = calls.map(c => z3.mkPattern(toZ3Formula(c, initialMap).get))

        val axiom : Z3AST = z3.mkForAll(0, patterns, namedBounds, quantBody)

        reporter.info("Look ! I made an axiom !")
        reporter.info(axiom.toString)
        solver.assertCnstr(axiom)
      }
    }
  }
}
