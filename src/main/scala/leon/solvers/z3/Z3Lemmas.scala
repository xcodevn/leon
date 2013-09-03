package leon
package solvers.z3

import z3.scala._

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._

trait Z3Lemmas {
  self : AbstractZ3Solver =>

  private lazy val lemmaPost = FreshIdentifier("res").setType(BooleanType)

  def prepareLemmas(solver : Z3Solver) : Unit = {
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

        reporter.info(" *** Multipatterns for lemma [%s].".format(fname))
        val z3MultiPatterns = for(mp <- multiPatterns) yield {
          reporter.info("--- ")
          reporter.info("--- " + mp.mkString("[", "; ", "]"))
      
          z3.mkPattern(
            mp.toSeq.map(c => toZ3Formula(c, initialMap).get) : _*
          ) 
        }

        val axiom : Z3AST = z3.mkForAll(0, z3MultiPatterns.toSeq, namedBounds, quantBody)

        reporter.info("Look ! I made an axiom !")
        reporter.info(axiom.toString)
        solver.assertCnstr(axiom)
      }}}
    }
  }


  /* This attempts to find a good set of patterns ("multipatterns") that will work
   * with Z3 E-Matching algorithm. Here are the rules:
   *   - patterns cannot contain interpreted symbols (and, or, plus, …).
   *     (but they *can* contain set membership, for instance)
   *
   *   - the sum of patterns (aka multipattern) must reference all free variables of
   *     the original expression
   *
   *   - patterns *should* be small (which means, more general)
   *
   *   - patterns *should* include all function terms of the expression, so that
   *     instantiation doesn't introduce new function terms (this design decision is
   *     up for debate). This should make --lemmas relatively predictable and
   *     efficient.
   *
   *     (Z3's pattern_inference.cpp has ~750 loc. That's encouraging.)
   */
  private def extractMultiPatterns(expr : Expr, vars : Set[Identifier]) : Set[Set[Expr]] = {
    def break(e : Expr) : Either[Expr,Set[Expr]] = e match {
      case And(es)            => Right(es.toSet)
      case Or(es)             => Right(es.toSet)
      case Not(e)             => Right(Set(e))
      case Implies(l,r)       => Right(Set(l,r))
      case Iff(l,r)           => Right(Set(l,r))
      case IfExpr(c,t,e)      => Right(Set(c,t,e))
      case Equals(l,r)        => Right(Set(l,r))
      case Plus(l,r)          => Right(Set(l,r))
      case Minus(l,r)         => Right(Set(l,r)) 
      case UMinus(e)          => Right(Set(e))
      case Times(l,r)         => Right(Set(l,r))
      case Division(l,r)      => Right(Set(l,r))
      case Modulo(l,r)        => Right(Set(l,r))
      case LessThan(l,r)      => Right(Set(l,r))
      case GreaterThan(l,r)   => Right(Set(l,r))
      case LessEquals(l,r)    => Right(Set(l,r))
      case GreaterEquals(l,r) => Right(Set(l,r)) 
      case _                  => Left(e)
    }

    // Needs to be improved...
    def isAcceptable(e : Expr) : Boolean = e match {
      case Variable(_) => false
      case IntLiteral(_) => false
      case BooleanLiteral(_) => false
      case CaseClassInstanceOf(_,_) => false
      case CaseClassSelector(_,_,_) => false
      case _ => true
    }

    def breakFP(e : Expr) : Set[Expr] = {
      var done : Set[Expr] = Set.empty
      var left : Set[Expr] = Set(e)

      while(!left.isEmpty) {
        val broken = left.map(break)
        left = Set.empty
        for(e <- broken) e match {
          case Left(ex)   => done += ex
          case Right(exs) => left ++= exs
        }
      }
      done
    }

    def coversAll(exprs : Iterable[Expr]) : Boolean = {
      !exprs.isEmpty && (exprs.map(variablesOf).reduceLeft(_ ++ _) == vars)
    }
    
    val bits = breakFP(expr).filter(isAcceptable)

    var ok : Set[Set[Expr]] = Set.empty

    for(bs <- bits.subsets) {
      if(coversAll(bs) && ok.forall(x => !x.subsetOf(bs))) {
        ok += bs
      }
    }

    ok
  }
}
