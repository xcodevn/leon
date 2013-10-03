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
import collection.mutable.{Map => MutableMap}

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

  private var stack : List[MutableList[RewriteRule]] = List(MutableList())

  def push() = {
    stack = (MutableList() ++ rules) :: stack 
    reporter.debug("Rewriter push()")
  }

  def pop() = {
    stack = stack.drop(1)
    reporter.debug("Rewriter pop(). Current rules")
    // pp_rules
  }

  def createPattern(lhs: Expr, rhs: Expr) = {
    // FIXME: do it later please 
  }

  class SilentReporter extends DefaultReporter(Settings()) {
    override def output(msg: String) : Unit = { }
  }

  var reporter: Reporter = new SilentReporter
  implicit val debugSection = DebugSectionSolver 

  def setReporter(rp: Reporter) = {
    reporter = rp
  }

  def pp_rules = {
    reporter.debug("List of current rules:")
    var c = 0
    for (ru <- rules) {
      c = c + 1
      reporter.debug("#%d\nName: %s\nConds: %s\nLHS: %s\nRHS: %s".format(c, ru.name, ru.conds.toString, ru.lhs.toString, ru.rhs.toString))
    }
  }

  def clearRules = rules.clear
  def instantiate(expr: Expr, m: MutableMap[Identifier, Expr]): Expr = expr match {
    case RewriteVariable(id) if m.contains(id) => {
      // println("Our map " + m + " map for id: "  + id + " to " + m(id))
      m(id)
    }

    case UnaryOperator(t, recons) => {
      recons(instantiate(t, m)).setType(expr.getType)

    }

    case BinaryOperator(t, y, recons) => {
      val i1 = instantiate(t, m)
      val i2 = instantiate(y, m)

      // println(" i1 i2 " + i1 + " : " + i2)
      recons(i1, i2).setType(expr.getType)
    }

    case n @ NAryOperator(args, recons) => {
      recons(args.map(ag => instantiate(ag, m))).setType(expr.getType)
    }

    case t @ _ => t

  }
  protected def rules = stack.head
  def resetRules = rules.clear
  def addRewriteRule(rule: RewriteRule) = {
    reporter.debug("Adding rewrite rule: ")
    reporter.debug("Name: %s\nConds: %s\nLHS: %s\nRHS: %s".format(rule.name, rule.conds.toString, rule.lhs.toString, rule.rhs.toString))
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
  def exprMatch(pattern: Expr, ex: Expr, map: MutableMap[Identifier, Expr]): Boolean = {
    def checkAndAdd(e: (Identifier,Expr)): Boolean = {
      if (map.contains(e._1)) {
        if (map(e._1).toString == e._2.toString)
          true
        else false
      } else {
        map += (e._1 -> e._2)
        true
      }
    }

    // println("Match \n" + pattern.toString  + " \n with \n" + ex.toString+ "\n===============\n")
    // println("Match type \n" + pattern.getType.toString  + " \n with type \n" + ex.getType.toString + "\n===============\n")
    // println("Match class \n" + pattern.getClass.toString  + " \n with type \n" + ex.getClass.toString + "\n===============\n")
    val t = leastUpperBound(pattern.getType, ex.getType)
    // println(t)
    val typ = t match {
      case Some(ty) if ty == pattern.getType => pattern.getType
      case _        => Untyped
    }


    if (pattern.getType == typ) {
      if (pattern.getClass != ex.getClass) {
        pattern match {
          case RewriteVariable(id) => 
            checkAndAdd( (id,ex) )
          case _            => false
        }
      } else {

        def checkChilds(args: Seq[Expr], args1: Seq[Expr]): Boolean = {
          for ((e1, e2) <- (args zip args1)) {
            if (!exprMatch(e1,e2, map)) 
              return false
          }
          true
        }

        pattern match {
          case CaseClassSelector(ccd, cc, cl) =>
            val CaseClassSelector(ccd1, cc1, cl1) = ex
            ccd == ccd1 && exprMatch(cc, cc1, map) && cl == cl1

          case FunctionInvocation(fd, args) => {
            val FunctionInvocation(fd1, args1) = ex
            if (fd == fd1) {
              checkChilds(args, args1)
            } else false
          }

          case UnaryOperator(t, recons) => {
            val UnaryOperator(t1,recons1) = ex
            exprMatch(t,t1, map)
          }
          case BinaryOperator(t, y, recons) => {
            val BinaryOperator(t1, y1, recons1) = ex
            val r1 = exprMatch(t,t1, map)
            if (r1) {
              val r2 = exprMatch(y,y1, map)
              r1 && r2
            } else false
          }
          case n @ NAryOperator(args, recons) => {
            val NAryOperator(args1, recons1) = ex
            if (args.size == args1.size) {
              checkChilds(args, args1)
            } else false
          }

          /* we don't need this when we change for using RewriteVarialbe instead of Variable as before
          case Variable(id) => {
            val Variable(id1) = ex
            checkAndAdd((id,ex))
          } 
          */

          case _ => pattern == ex
        }
      }
    } else false

  }

  def simplify(sf: SolverFactory[Solver])(old_expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT) = {
    // println("Simplify: " + expr.toString)
    val solver = SimpleSolverAPI(sf.withTimeout(10L))
    val (expr,rl) = old_expr match {
      case Implies(e1, e2) => {
        val (ex, rl) = simplify(sf)(e2, proofContext)
        (Implies(e1, ex).setType(old_expr.getType), SIMP_SUCCESS())
      }

      case UnaryOperator(t, recons) => {
        val (ex, rl) = simplify(sf)(t, proofContext)
        (recons(ex).setType(old_expr.getType), SIMP_SUCCESS())
      }

      case BinaryOperator(t, y, recons) => {
        val (ex1, rl1) = simplify(sf)(t, proofContext)
        val (ex2, rl2) = simplify(sf)(y, proofContext)
        (recons(ex1, ex2).setType(old_expr.getType), SIMP_SUCCESS())
      }

      case n @ NAryOperator(args, recons) => {
        (recons(args.map ( ar => { val (ex, rl) = simplify(sf)(ar, proofContext); ex } )).setType(old_expr.getType), SIMP_SUCCESS())
      }

      case _ => (old_expr, SIMP_SUCCESS())
    }

    def rewriteVariablesOf(e: Expr): Set[Identifier] = e match {
      case RewriteVariable(id)  => Set(id)

      case UnaryOperator(t, recons) => {
        rewriteVariablesOf(t)
      }

      case BinaryOperator(t, y, recons) => {
        rewriteVariablesOf(t) ++ rewriteVariablesOf(y)
      }

      case n @ NAryOperator(args, recons) => {

        args.foldLeft(Set[Identifier]()) ( (curSet, elem) => curSet ++ rewriteVariablesOf(elem) )
      }

      case t @ _ => Set()
    }

    for ( rule @ RewriteRule(rname, conds, lhs, rhs, w) <- rules.sortWith(_.weight > _.weight)) {
      val varsInLHS = rewriteVariablesOf(lhs)

      val m: MutableMap[Identifier, Expr] = MutableMap.empty
      val isMatched = exprMatch(lhs, expr, m)
      if (isMatched) {
        // println ("Matched " + lhs + " with " + expr + " \n Map is " + m)
        def isSubSimplify(expr: Expr): Boolean = {
          expr match {
          case Equals(_, v @ RewriteVariable(id))  if !varsInLHS.contains(id) => true
          case Iff(_, v @ RewriteVariable(id))  if !varsInLHS.contains(id) => true
          case Implies(_, Equals(_, v @ RewriteVariable(id)))  if !varsInLHS.contains(id) => true
          case Implies(_, Iff(_, v @ RewriteVariable(id)))  if !varsInLHS.contains(id) => true
          case _ => false
        }
        }

        def toRewriteRule(expr: Expr): RewriteRule = expr match {
          case Equals(lhs, rhs @ RewriteVariable(id)) if !varsInLHS.contains(id) => RewriteRule("somename", Seq(), lhs, rhs,0)
          case Iff(lhs, rhs @ RewriteVariable(id)) if !varsInLHS.contains(id) => RewriteRule("somename", Seq(), lhs, rhs,0)
          case Implies(And(conds), Equals(lhs, rhs @ RewriteVariable(id)))  if !varsInLHS.contains(id) => RewriteRule("somename", conds, lhs, rhs,0)
          case Implies(And(conds), Iff(lhs, rhs @ RewriteVariable(id)))  if !varsInLHS.contains(id) => RewriteRule("somename", conds, lhs, rhs,0)
          case Implies(cond, Equals(lhs, rhs @ RewriteVariable(id)))  if !varsInLHS.contains(id) => RewriteRule("somename", Seq(cond), lhs, rhs, 0)
          case Implies(cond, Iff(lhs, rhs @ RewriteVariable(id)))  if !varsInLHS.contains(id) => RewriteRule("somename", Seq(cond), lhs, rhs, 0)
          case _ => {
            // println(expr)
            throw new Throwable("We don't want this case!")

          }
        }

        val realConds = conds.filter(!isSubSimplify(_)).map(cond => instantiate(cond, m))
        // println("Real conds : " + realConds)
        reporter.debug("check SAT " + And(Seq(Not(And(realConds))) ++ proofContext))
        val rl = try {
          solver.solveSAT(And(Seq(Not(And(realConds))) ++ proofContext)) 
        } catch { case _ : Throwable => (Some(true), true) }

        rl match {
          case (Some(false),_)  =>
            val newM = m ++ conds.filter(isSubSimplify(_)).foldLeft (Map[Identifier,Expr]()) ( (curVal, cond) =>{
              val RewriteRule(rname1, conds1, lhs1, rhs1, w) = toRewriteRule(cond)
              val RewriteVariable(id) = rhs1
              lhs1 match {
                case RewriteVariable(idd) if m.contains(idd) && conds1.size == 0 => curVal + (id -> m(idd))
                case _ => 
                  val new_lhs1 = instantiate(lhs1, m)
                  val new_conds1 = instantiate(And(conds1), m)
                  def findingRule(e: Expr): Seq[RewriteRule] = e match {
                    case And(lst) => lst.foldLeft( Seq[RewriteRule]() ) ( (cur, elem) => cur ++ findingRule(elem) )
                    case Equals(e1, e2) => Seq(RewriteRule("localassumption", Seq(), e1, e2, 25))
                    case Iff(e1, e2) => Seq(RewriteRule("localassumption", Seq(), e1, e2, 25))
                    case _ => Seq()
                  }

                  def findingCCS(e: Expr): Seq[CaseClassInstanceOf] = e match {
                    case ccs : CaseClassInstanceOf => Seq(ccs)
                    case And(lst) => lst.map(l => findingCCS(l)).foldLeft(Seq[CaseClassInstanceOf]()) ( (cur, elem) => cur ++ elem)
                    case _ =>  Seq()
                  }

                  reporter.debug("Cond " + new_conds1)
                  SimpleRewriter.push()
                  for (r <- findingRule(new_conds1)) SimpleRewriter.addRewriteRule(r)

                  var extraConds = Seq[Expr]()
                  var invExtraConds = Seq[Expr]()

                  for (ccs <- findingCCS(new_conds1)) {
                    val CaseClassInstanceOf(cd, ex) = ccs
                    val CaseClassDef(i, p, f)  = cd
                    def getNewVariable(vd: VarDecl): Variable = {
                      val VarDecl(id, ty) = vd
                      Variable(FreshIdentifier(ex.toString+"_"+id.toString).setType(ty))
                    }
                    val nl = f.map( elem => getNewVariable(elem))
                    val csl = f.map (el => { val VarDecl(id, ty) = el; CaseClassSelector(cd, ex, id)})
                    val se1 = nl.zip(csl).map ( el => { val (v, cl) = el; Equals(cl, v) } )
                    val invse1 = nl.zip(csl).map ( el => { val (v, cl) = el; Equals(v, cl) } )
                    val ma = Equals(ex, CaseClass(cd, nl.toSeq))
                    val invma = Equals(CaseClass(cd, nl.toSeq), ex)
                    extraConds = extraConds ++ Seq(ma) ++ se1
                    invExtraConds = invExtraConds ++ Seq(invma) ++ invse1
                  }

                  for (r <- findingRule(And(extraConds))) SimpleRewriter.addRewriteRule(r)

                  val (s_lhs11, rl1) = simplify(sf)(new_lhs1, extraConds ++ Seq(new_conds1) ++ proofContext)
                  SimpleRewriter.pop()

                  SimpleRewriter.push()
                  for (r <- findingRule(And(invExtraConds))) SimpleRewriter.addRewriteRule(r)
                  val (s_lhs12, rl2) = simplify(sf)(s_lhs11, invExtraConds ++ Seq(new_conds1) ++ proofContext)
                  SimpleRewriter.pop()
                  // println("Add new elem: "+ (id, s_lhs1))
                  curVal + (id -> s_lhs12)
              }
            })
            // println("New Map : " + newM+ " used for RHS : " + rhs)
            val new_rhs = instantiate(rhs, newM)
            // println("after instantiate " + rhs + " became " + new_rhs)
            reporter.debug("By using rule: \n" + rule + "\nwe simplify \n====\n" + expr + "\n----\ninto\n----\n" + new_rhs + "\n====")
            return (new_rhs, SIMP_SUCCESS())
          case _ => 
        }
      }
    }

    (expr, rl)
  }
}
