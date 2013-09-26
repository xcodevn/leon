// A Rewriter for simp_tac

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

abstract class SIMPRESULT
case class SIMP_SUCCESS() extends SIMPRESULT
case class SIMP_SAME()    extends SIMPRESULT
case class SIMP_FAIL(msg: String) extends SIMPRESULT

// FIXME: lhs: should be a PATTERN
case class RewriteRule (val name: String, val conds: Seq[Expr], val lhs: Expr, val rhs: Expr, val weight: Int)

//
// This class is built base on Solver.scala
// We need a stable API for Rewriters
//
abstract class Rewriter {
  // This function will return a subset of lemmas which are really necessary for proof of `conjecture`

  def createPattern(lhs: Expr, rhs: Expr) = {
    // FIXME: do it later please 
  }

  def pp_rules: String = {
    println("List of current rules:")
    var c = 1
    val s = for (ru <- rules) yield {
      c = c + 1
      "#%d\nName: %s\nConds: %s\nLHS: %s\nRHS: %s".format(c, ru.name, ru.conds.toString, ru.lhs.toString, ru.rhs.toString)
    }
    s.mkString("\n")
  }

  def clearRules = rules.clear
  def instantiate(expr: Expr, m: Map[Identifier, Expr]): Expr = expr match {
    case Variable(id) if m.contains(id) => {
      // println("Our map " + m + " map for id: "  + id + " to " + m(id))
      m(id)
    }

    case UnaryOperator(t, recons) => {
      recons(instantiate(t, m))
    }

    case BinaryOperator(t, y, recons) => {
      val i1 = instantiate(t, m)
      val i2 = instantiate(y, m)

      // println(" i1 i2 " + i1 + " : " + i2)
      recons(i1, i2)
    }

    case n @ NAryOperator(args, recons) => {
      recons(args.map(ag => instantiate(ag, m)))
    }

    case t @ _ => t

  }
  protected val rules : MutableList[RewriteRule] = new MutableList[RewriteRule]
  def resetRules = rules.clear
  def addRewriteRule(rule: RewriteRule) = {
    rules += rule
  }

  def simplify(sf: SolverFactory[Solver])(expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT)
}

object TrivialRewriter1 extends Rewriter {
  def simplify(sf: SolverFactory[Solver])(expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT) = {
    (Error("Not implemented yet!"), SIMP_FAIL("unknown reason"))
  }
}

object TrivialRewriter2 extends Rewriter {
  def simplify(sf: SolverFactory[Solver])(expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT) = {
    (expr, SIMP_SUCCESS())
  }
}
object SimpleRewriter extends Rewriter {
  def exprMatch(pattern: Expr, ex: Expr): (Boolean, Map[Identifier,Expr]) = {

    // println("Match \n" + pattern.toString  + " \n with \n" + ex.toString+ "\n===============\n")
    // println("Match type \n" + pattern.getType.toString  + " \n with type \n" + ex.getType.toString + "\n===============\n")
    val t = leastUpperBound(pattern.getType, ex.getType)
    // println(t)
    val typ = t match {
      case Some(ty) if ty == pattern.getType => pattern.getType
      case _        => Untyped
    }

    if (pattern.getType == typ) {
      if (pattern.getClass != ex.getClass) {
        pattern match {
          case Variable(id) => (true, Map(id -> ex) )
          case _            => (false, Map())
        }
      } else {

        def checkChilds(args: Seq[Expr], args1: Seq[Expr]): (Boolean, Map[Identifier, Expr]) = {
          val rl = for ((e1, e2) <- (args zip args1)) yield exprMatch(e1,e2)
          (rl.map(_._1).foldLeft(true)((cur, va) => cur && va), 
            rl.map(_._2).foldLeft(Map[Identifier,Expr]())((cur, va) => cur ++ va))
        }

        pattern match {
          case FunctionInvocation(fd, args) => {
            val FunctionInvocation(fd1, args1) = ex
            if (fd == fd1) {
              checkChilds(args, args1)
            } else (false, Map())
          }

          case UnaryOperator(t, recons) => {
            val UnaryOperator(t1,recons1) = ex
            exprMatch(t,t1)
          }
          case BinaryOperator(t, y, recons) => {
            val BinaryOperator(t1, y1, recons1) = ex
            val (r1, m1) = exprMatch(t,t1)
            if (r1) {
              val (r2, m2) = exprMatch(y,y1)
              (r1 && r2, m1 ++ m2)
            } else (false, Map())
          }
          case n @ NAryOperator(args, recons) => {
            val NAryOperator(args1, recons1) = ex
            if (args.size == args1.size) {
              checkChilds(args, args1)
            } else (false, Map())
          }

          case Variable(id) => {
            val Variable(id1) = ex
            (true, Map (id -> ex))
          }

          case _ => (pattern == ex, Map())
        }
      }
    } else (false, Map())

  }

  def simplify(sf: SolverFactory[Solver])(old_expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT) = {
    // println("Simplify: " + expr.toString)
    val solver = SimpleSolverAPI(sf.withTimeout(100L))
    val (expr,rl) = old_expr match {
      case UnaryOperator(t, recons) => {
        val (ex, rl) = simplify(sf)(t, proofContext)
        (recons(ex), SIMP_SUCCESS())
      }

      case BinaryOperator(t, y, recons) => {
        val (ex1, rl1) = simplify(sf)(t, proofContext)
        val (ex2, rl2) = simplify(sf)(y, proofContext)
        (recons(ex1, ex2), SIMP_SUCCESS())
      }

      case n @ NAryOperator(args, recons) => {
        (recons(args.map ( ar => { val (ex, rl) = simplify(sf)(ar, proofContext); ex } )), SIMP_SUCCESS())
      }

      case _ => (old_expr, SIMP_SUCCESS())
    }
    for (RewriteRule(rname, conds, lhs, rhs, w) <- rules.sortWith(_.weight > _.weight)) {
      val varsInLHS = variablesOf(lhs)
      val (isMatched, m) = exprMatch(lhs, expr)
      if (isMatched) {
        // println ("Matched " + lhs + " with " + expr + " \n Map is " + m)
        def isSubSimplify(expr: Expr): Boolean = {
          expr match {
          case Equals(_, v @ Variable(id)) if !varsInLHS.contains(id) => true
          case Implies(_, Equals(_, v @ Variable(id))) if !varsInLHS.contains(id) => true
          case _ => false
        }
        }

        def toRewriteRule(expr: Expr): RewriteRule = expr match {
          case Equals(lhs, rhs @ Variable(id)) if !varsInLHS.contains(id) => RewriteRule("somename", Seq(), lhs, rhs,0)
          case Implies(And(conds), Equals(lhs, rhs @ Variable(id))) if !varsInLHS.contains(id) => RewriteRule("somename", conds, lhs, rhs,0)
          case Implies(cond, Equals(lhs, rhs @ Variable(id))) if !varsInLHS.contains(id) => RewriteRule("somename", Seq(cond), lhs, rhs, 0)
          case _ => {
            println(expr)
            throw new Throwable("We don't want this case!")

          }


        }

        val realConds = conds.filter(!isSubSimplify(_)).map(cond => instantiate(cond, m))
        // println("Real conds : " + realConds)
        // println("check SAT " + And(Seq(Not(And(realConds))) ++ proofContext))
        solver.solveSAT(And(Seq(Not(And(realConds))) ++ proofContext)) match {
          case (Some(false),_)  =>
            val newM = m ++ conds.filter(isSubSimplify(_)).foldLeft (Map[Identifier,Expr]()) ( (curVal, cond) =>{
              val RewriteRule(rname1, conds1, lhs1, rhs1, w) = toRewriteRule(cond)
              val new_lhs1 = instantiate(lhs1, m)
              val new_conds1 = instantiate(And(conds1), m)
              val (s_lhs1, rl) = simplify(sf)(new_lhs1, Seq(new_conds1) ++ proofContext)
              val Variable(id) = rhs1
              // println("Add new elem: "+ (id, s_lhs1))
              curVal + (id -> s_lhs1)
            })
            // println("New Map : " + newM+ " used for RHS : " + rhs)
            val new_rhs = instantiate(rhs, newM)
            // println("after instantiate " + rhs + " became " + new_rhs)
            println("By using rule: " + rname + " we simplify \n====\n" + expr + "\n----\ninto\n----\n" + new_rhs + "\n====")
            return (new_rhs, SIMP_SUCCESS())
          case _ => 
        }
      }
    }

    (expr, rl)
  }
}
