package leon
package solvers.z3

import z3.scala._
import scala.collection.mutable.MutableList

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._
import leon.purescala.Definitions._

object LemmaTools {
  def isTrueLemma(funDef: FunDef): Boolean = {
    if (!funDef.annotations.contains("lemma")) false
    else {
      val fname = funDef.id.name

      if (!(funDef.returnType == BooleanType)) {
        false
      } else {
        funDef.postcondition match {
          case None =>
            false
          case Some((id, post)) =>
            if (id.getType != BooleanType) {
              false
            }
            else {
              funDef.implementation match {
                case None =>
                  false
                case Some(imple) => true
              }
            }
        }
      }
    }
  }
}

trait Z3Lemmas {
  self : AbstractZ3Solver =>

  private lazy val lemmaPost = FreshIdentifier("res").setType(BooleanType)

  val lemmaZ3ASTs: MutableList[Z3AST] = new MutableList[Z3AST]()

  def prepareLemmas(solver: Z3Solver, funDefs: Seq[FunDef]): Unit = {
    for (funDef <- funDefs) {
      if (LemmaTools.isTrueLemma(funDef)) {
        val fname = funDef.id.name
        funDef.implementation match {
          case None =>
          case Some(imple) =>
          // So this looks like a good lemma :D
          reporter.info("Yeepee! [%s] is a nice lemma!".format(fname))

          val lemmaBody: Expr = funDef.precondition.map { pre =>
            Implies(pre, imple)
          } getOrElse {
            imple
          }

          val fArgs: Seq[Variable] = funDef.args.map(_.toVariable)
          val argSorts: Seq[Z3Sort] = fArgs.map(v => typeToSort(v.getType))
          val bounds: Seq[Z3AST] = argSorts.zipWithIndex.map { case (s, i) => z3.mkBound(i, s) }
          val namedBounds: Seq[(Z3Symbol, Z3Sort)] = argSorts.map(a => (z3.mkFreshStringSymbol("qx"), a))
          val initialMap: Map[Identifier, Z3AST] = fArgs.map(_.id).zip(bounds).toMap

          // FIXME : that ".get" is bolder that we want it to be.
          // Also: Apply matchToIfThenElse and let-expansion
          val quantBody: Z3AST = toZ3Formula(matchToIfThenElse(lemmaBody), initialMap).get

          val varSet: Set[Identifier] = fArgs.map(_.id).toSet
          val preMps: Set[Set[Expr]] = funDef.precondition match {
            case Some(precond) =>
              extractMultiPatterns(matchToIfThenElse(precond), varSet)
            case None =>
              Set.empty
          }

          val multiPatterns: Set[Set[Expr]] = if (!preMps.isEmpty) {
            preMps
          } else {
            extractMultiPatterns(matchToIfThenElse(lemmaBody), varSet)
          }

          // reporter.info(" *** Multipatterns for lemma [%s].".format(fname))
          if (!multiPatterns.isEmpty) {
            val lst = for (mp <- multiPatterns) yield {
              // reporter.info("--- ")
              // reporter.info("--- " + mp.mkString("[", "; ", "]"))

              mp.toSeq.map(c => toZ3Formula(c, initialMap).get)
            }

            // reporter.info(lst.toSeq)

            val z3MultiPatterns = z3.mkPattern(lst.toSeq.flatten: _*)

            val axiom: Z3AST = z3.mkForAll(0, Seq(z3MultiPatterns), namedBounds, quantBody)

            // reporter.info("Look ! I made an axiom !")
            // reporter.info(axiom.toString)

            lemmaZ3ASTs += axiom // re-use latter
            // solver.assertCnstr(axiom)
          } else {
            val axiom: Z3AST = z3.mkForAll(0, Seq(), namedBounds, quantBody)

            // reporter.info("Look ! I made an axiom !")
            // reporter.info(axiom.toString)
            solver.assertCnstr(axiom)
          }
        }
      } else {
          reporter.error("[%s] is NOT a nine lemma!".format(funDef.id.name))
      }
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
