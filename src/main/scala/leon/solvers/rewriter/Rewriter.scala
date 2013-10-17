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
import collection.mutable.{Map => MutableMap, Set => MutableSet}

abstract class SIMPRESULT
case class SIMP_SUCCESS() extends SIMPRESULT
case class SIMP_SAME()    extends SIMPRESULT
case class SIMP_FAIL(msg: String) extends SIMPRESULT

// FIXME: lhs: should be a PATTERN
case class RewriteRule (val name: String, val conds: Seq[Expr], val lhs: Expr, val rhs: Expr, val weight: Int) {
  var isPermutation = false
  def enablePermutation() = { isPermutation = true }
  def disablePermutation() = { isPermutation = false }
}

//
// This class is built base on Solver.scala
// We need a stable API for Rewriters
//
abstract class Rewriter {
  // This function will return a subset of lemmas which are really necessary for proof of `conjecture`

  private var stack : List[MutableMap[String, Seq[RewriteRule]]] = List(MutableMap())

  var t: Long = -1

  def startTimer = {
   t = System.currentTimeMillis
  }

  def TIMEOUT = 1000 /* default is 1 sec */

  private var doTimeout: Boolean = true

  def disableTimeout() = { doTimeout = false }
  def enableTimeout()  = { doTimeout = true  }

  def isTimeout = ( System.currentTimeMillis - t > TIMEOUT ) && (t != -1) && doTimeout

  def push() = {
    stack = (MutableMap() ++ rules) :: stack 
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
    for (ru <- rules.values.flatten) {
      c = c + 1
      reporter.debug("#%d\nName: %s\nConds: %s\nLHS: %s\nRHS: %s".format(c, ru.name, ru.conds.toString, ru.lhs.toString, ru.rhs.toString))
    }
  }

  def clearRules = rules.clear
  def instantiate(expr: Expr, m: MutableMap[Identifier, Expr]): Expr = {
    // println("ins " + expr + "  use  " + m)
    expr match {
      case FunctionInvocation(fd, args) => {
        FunctionInvocation(fd, args.map(ag => instantiate(ag, m)), false)
      }
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
  }
  def exprHash(e: Expr): String = {
    e match {
      case FunctionInvocation(fd, _) => fd.id.toString
      case CaseClassSelector(ccd, cc, cl) => ccd.id.toString + "." + cl.toString
      case CaseClass(ccd, _) => ccd.id.toString
      case v : Variable       => v.toString
      case t : BooleanLiteral => t.toString
      case t : IntLiteral => t.toString
      case t @ _ => t.getClass.getSimpleName
    }
  }

  def hashRule(r: RewriteRule): String = exprHash(r.lhs)

  protected def rules = stack.head
  def resetRules = rules.clear

  def addRewriteRule(rule: RewriteRule) = {
    reporter.debug("Adding rewrite rule: ")
    reporter.debug("Name: %s\nConds: %s\nLHS: %s\nRHS: %s\nIs permutation: %s".format(rule.name, rule.conds.toString, rule.lhs.toString, rule.rhs.toString, rule.isPermutation))
    val str = hashRule(rule)
    val old_rule = rules.getOrElse(str, Seq[RewriteRule]())
    rules.update(str, old_rule :+ rule)
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

class SimpleRewriter extends Rewriter {

  val sop: MutableSet[RewriteRule] = MutableSet.empty
  def getSOPRules() : Set[RewriteRule] = sop.toSet
  def isPermutationRule(r: RewriteRule): Boolean = {
    val m: MutableMap[Identifier, Expr] = MutableMap.empty
    if (r.conds.size == 0)  {
      /*val rl = */
     exprMatch(r.lhs, r.rhs, m)
      // println (" matching "  + r.lhs + " with  " + r.rhs + " result " + rl)
      // rl
    }
    else false
  }
  override def addRewriteRule(rule: RewriteRule) = {
    if (isPermutationRule(rule)) rule.enablePermutation
    super.addRewriteRule(rule)
  }
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
      if (pattern.getClass != ex.getClass || ex.isInstanceOf[RewriteVariable] ) {   
        /* second case of OR is for permutation rewrite rule, if we have problem later, FIXME */
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

  def simplifyWithSolver(sf: SimpleSolverAPI)(old_expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT) = {
    // println("Simplify: " + old_expr.toString)
    // val solver = SimpleSolverAPI(sf)
    val (expr,rl) = old_expr match {
      case And(lst) => {
        val (newlst, rllst) = lst.map(simplifyWithSolver(sf)(_, proofContext)).unzip
        /* trying to simplify true, false cases */
        val e = {
          if (newlst.forall(e => e == BooleanLiteral(true))) BooleanLiteral(true)
          else if (! newlst.forall(e => e != BooleanLiteral(false))) BooleanLiteral(false)
          else And(newlst)
        }

        if (rllst.forall(_ == SIMP_SUCCESS()))
          (e, SIMP_SUCCESS())
        else (e, SIMP_FAIL("Fail"))
      }

      case t @ CaseClassInstanceOf(cd, ex) => {
        val (e, r) = simplifyWithSolver(sf)(ex, proofContext)
        e match {
          case CaseClass(ccd, e1) => {
            val cd1 = classDefToClassType(cd)
            val cd2 = classDefToClassType(ccd)
            if (isSubtypeOf(cd2, cd1)) (BooleanLiteral(true), r) else (BooleanLiteral(false), r)
          }
          case _ => (CaseClassInstanceOf(cd, e), r)
        }
      }
      case Implies(e1, e2) => {
        val (ex, rl) = simplifyWithSolver(sf)(e2, proofContext)
        (Implies(e1, ex).setType(old_expr.getType), rl)
      }

      case UnaryOperator(t, recons) => {
        val (ex, rl) = simplifyWithSolver(sf)(t, proofContext)
        (recons(ex).setType(old_expr.getType), rl)
      }

      case BinaryOperator(t, y, recons) => {
        val (ex1, rl1) = simplifyWithSolver(sf)(t, proofContext)
        val (ex2, rl2) = simplifyWithSolver(sf)(y, proofContext)
        val rl = if (rl1 == SIMP_SUCCESS() && rl2 == SIMP_SUCCESS() ) SIMP_SUCCESS() else SIMP_FAIL("Binary simp failed")
        (recons(ex1, ex2).setType(old_expr.getType), rl)
      }

      case n @ NAryOperator(args, recons) => {
        var isSucc = true
        val nargs = for (ar <- args) yield {
          val (ex, rl) = simplifyWithSolver(sf)(ar, proofContext)
          if (rl == SIMP_SUCCESS()) ex 
          else { isSucc= false; ex}
        }

        if (isSucc) (recons(nargs).setType(old_expr.getType), SIMP_SUCCESS())
        else (recons(nargs).setType(old_expr.getType), SIMP_FAIL("FAIL"))
      }

      case _ => (old_expr, SIMP_SUCCESS())
    }

    if (rl != SIMP_SUCCESS()) return (expr, rl)

    /* We check timeout at this point */
    if (isTimeout) {
      reporter.debug("Simplify TIMEOUT")
      return (expr, rl)
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

    // println(exprHash(expr))
    val rs = rules.getOrElse(exprHash(expr), Seq())
    // println(rs)

    for ( rule @ RewriteRule(rname, conds, lhs, rhs, w) <- rs.sortWith(_.weight > _.weight)) {
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

        // println("pC.S " + proofContext.size)
        val realConds = conds.filter(!isSubSimplify(_)).map(cond => instantiate(cond, m))
        // println ("real conds " + realConds)
        val simplified_realConds = realConds.map(x => {
          // println("Begin s " + x)
          push()
          // SimpleRewriter.clearRules  // why we have to clear ?
          val (eee, rll) = simplifyWithSolver(sf)(x, Seq())
          pop()
          // println("End s " + eee)
          eee

        })
        // println("pC.S " + proofContext.size)
        val rl = try {
          if (simplified_realConds.forall(x => x == BooleanLiteral(true))) (Some(false), 1)
          else if (!simplified_realConds.forall(x => ! (x == BooleanLiteral(false)))) (Some(true), 1)
          else if (proofContext.size > 0) {
            // println("check SAT " + Not(And(realConds)).toString + " with context " + proofContext.toString)
            // val rl = sf.solveSAT(And(Seq(Not(And(realConds))) ++ proofContext)) 
            val rl = (Some(true), 2)
            /*
            rl match {
              case (Some(false), _) => println("check SAT TRUE " + realConds + " with proof " + proofContext)
              case _ => println("check SAT FALSE " + realConds + " with proof " + proofContext)

            }
            */
            rl
          } else (None, 2)
        } catch { case _ : Throwable => return (expr, SIMP_FAIL("Solver does not know expression")) }
        // println("rl " + rl)

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
                  push()
                  clearRules /* We only use translation rules */

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

                  for (r <- findingRule(And(extraConds))) addRewriteRule(r)
                  /* Convert into new form */
                  disableTimeout()
                  val (s_lhs111, rl11) = simplifyWithSolver(sf)(new_lhs1, Seq())
                  enableTimeout()
                  pop()

                  /* Real simplify */
                  push()
                  for (r <- findingRule(new_conds1)) addRewriteRule(r)
                  val (s_lhs11, rl1) = simplifyWithSolver(sf)(s_lhs111, extraConds ++ Seq(new_conds1) ++ proofContext)
                  pop()

                  /* Convert into original form */
                  push()
                  clearRules             /* We don't want any other rules effect this process */
                  disableTimeout()
                  for (r <- findingRule(And(invExtraConds))) addRewriteRule(r)
                  val (s_lhs12, rl2) = simplifyWithSolver(sf)(s_lhs11, Seq())
                  enableTimeout()
                  pop()
                  // println("Add new elem: "+ (id, s_lhs1))
                  curVal + (id -> s_lhs12)
              }
            })
            // reporter.debug("New Map : " + newM+ " used for RHS : " + rhs)
            val new_rhs = instantiate(rhs, newM)
            // println("after instantiate " + rhs + " became " + new_rhs)
            if (!rule.isPermutation) {
              reporter.debug("By using rule: \n" + rule + "\nwe simplify \n====\n" + expr + "\n----\ninto\n----\n" + new_rhs + "\n====")
              sop += rule
              return (new_rhs, SIMP_SUCCESS())
            } else if (expr.toString < new_rhs.toString) {
                reporter.debug("By using permutation rule: \n" + rule + "\nwe simplify \n====\n" + expr + "\n----\ninto\n----\n" + new_rhs + "\n====")
                sop += rule
                return (new_rhs, SIMP_SUCCESS())
              }
          case _ => 
        }
      }
    }

    (expr, rl)
  }

  def simplify(sf: SolverFactory[Solver])(expr: Expr, proofContext: Seq[Expr]): (Expr, SIMPRESULT) = {
    simplifyWithSolver(SimpleSolverAPI(sf))(expr, proofContext)
  }

}
