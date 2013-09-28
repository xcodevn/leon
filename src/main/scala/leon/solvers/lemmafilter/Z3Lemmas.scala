package leon
package solvers.lemmafilter

import z3.scala._
import leon.solvers.z3._
import scala.collection.mutable.MutableList

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._
import leon.purescala.Definitions._
import leon.solvers._

class ExtendedFairZ3Solver(context : LeonContext, program: Program) extends FairZ3SolverFactory(context, program) {

  val (lemmaFlag, filterOption, numLemmasOption) = locally {
    var lemmaFlag = false
    var filterOption = "NOTUSED"
    var numLemmasOption = 2
    for(opt <- context.options) opt match {
      case LeonFlagOption("lemmas", v)             => lemmaFlag           = v
      case LeonValueOption("filter", v)            => { filterOption = v; if (v=="MaSh" || v == "MePo") lemmaFlag = true }
      case LeonValueOption("num-lemmas", v)        => numLemmasOption = v.toInt
        
      case _ =>
    }
    (lemmaFlag, filterOption, numLemmasOption)
  }

  override def getNewSolver = {
    val solver = super.getNewSolver
    new Solver {
      var addLemmaYet = false
      def interrupt = solver.interrupt
      def recoverInterrupt = solver.recoverInterrupt
      def assertCnstr(expression: leon.purescala.Trees.Expr): Unit = {
        solver.assertCnstr(expression)
        if (!addLemmaYet)
          filter(expression)
        addLemmaYet = true
      }
      def check = solver.check
      def checkAssumptions(assumptions: Set[leon.purescala.Trees.Expr]) = solver.checkAssumptions(assumptions)
      def getModel = solver.getModel
      def getUnsatCore = solver.getUnsatCore
      def pop(lvl: Int) = solver.pop(lvl)
      def push = solver.push
    }
  }

  def filter(expression: Expr) = {
    /* Only use filter in the first time of calling this function */
    if(lemmaFlag) {
      filterOption match {
        case "MaSh" =>
          val MaShfilter = new MaShFilter(context, program)
          val curFun = program.definedFunctions.filter(f=>f.isReach).sortWith( (fd1,fd2) => fd1 < fd2 ).reverse.head
          val funs = curFun +: program.definedFunctions.filter(f => f < curFun)
          if (curFun.annotations.contains("depend")) {
            curFun.dependencies match { case Some(deps) => prepareLemmas(funs.filter(f => deps.contains(f.id.name.toString))); case _ => }
          } else {
            val m = funs.tail.filter(f => f.annotations.contains("lemma")).map( f => (f, Error(":-)"))).toMap
            if (m.size > 0)
              prepareLemmas(MaShfilter.filter(expression, m, numLemmasOption) )
          }
          MaShfilter.fairZ3.free() // go away z3 ;)

        case "MePo" =>
          val MePofilter = new MePoFilter(context, program)
          val curFun = program.definedFunctions.filter(f=>f.isReach).sortWith( (fd1,fd2) => fd1 < fd2 ).reverse.head
          val funs = curFun +: program.definedFunctions.filter(f => f < curFun)
          if (curFun.annotations.contains("depend")) {
            curFun.dependencies match { case Some(deps) => prepareLemmas(funs.filter(f => deps.contains(f.id.name.toString))); case _ => }
          } else {
            val m = funs.tail.filter(f => f.annotations.contains("lemma")).map( f => (f, MePofilter.genVC(f))).toMap
            if (m.size > 0) {
              val res = MePofilter.filter(expression, m, numLemmasOption)
              prepareLemmas(res)
            }
          }
          MePofilter.fairZ3.free() // I don't need you anymore

        case _ =>
          prepareLemmas(program.definedFunctions.filter(f=> f.annotations.contains("lemma"))) /* As before I come here ;) */
      }
    }
  }

  def unfold(expr: Expr, times: Int): Seq[Z3AST] = {
    val unrollingBank = new UnrollingBank()
    val newClauses = unrollingBank.scanForNewTemplates(expr)

    val cl = for (c <- 0 until times) yield {
      val toRelease = unrollingBank.getZ3BlockersToUnlock

      val kk = for (id <- toRelease) yield {
        unrollingBank.unlock(id)
      }
      kk.flatten
    }

    newClauses ++ cl.flatten
  }

  def prepareLemmas(funDefs: Seq[FunDef]): Unit = {
    val lemmaZ3ASTs: MutableList[Z3AST] = new MutableList[Z3AST]()
    for (funDef <- funDefs) {
      if (LemmaTools.isTrueLemma(funDef)) {
        val fname = funDef.id.name
        funDef.implementation match {
          case None =>
          case Some(imple) =>
          // So this looks like a good lemma :D
          // reporter.info("Yeepee! [%s] is a nice lemma!".format(fname))

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

            val axiom: Z3AST = z3.mkForAll(11, Seq(z3MultiPatterns), namedBounds, quantBody)

            // reporter.info("Look ! I made an axiom !")
            // reporter.info(axiom.toString)

            lemmaZ3ASTs += axiom // re-use latter
            // solver.assertCnstr(axiom)
          } else {
            val axiom: Z3AST = z3.mkForAll(11, Seq(), namedBounds, quantBody)

            // reporter.info("Look ! I made an axiom !")
            // reporter.info(axiom.toString)
            // solver.assertCnstr(axiom)
          }
        }
      } else {
          // reporter.error("[%s] is NOT a nine lemma!".format(funDef.id.name))
      }
    }

    if (lemmaZ3ASTs.size > 0) lemmas = Some(lemmaZ3ASTs)
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
