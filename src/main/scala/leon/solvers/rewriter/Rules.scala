// List of base rules for Leon
//
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

object Rules {
  def addDefaultRules(rewriter: Rewriter) {
    val p = RewriteVariable(FreshIdentifier("cond")).setType(BooleanType)
    val n1 = RewriteVariable(FreshIdentifier("n1")).setType(Int32Type)
    val n2 = RewriteVariable(FreshIdentifier("n2")).setType(Int32Type)
    val e1= RewriteVariable(FreshIdentifier("e1"))
    val e2= RewriteVariable(FreshIdentifier("e2"))
    val rve1= RewriteVariable(FreshIdentifier("rve1"))
    val rve2= RewriteVariable(FreshIdentifier("rve2"))
    val rvp= RewriteVariable(FreshIdentifier("rvp"))
    val iteExpr = IfExpr(p, e1, e2)
    val truee = BooleanLiteral(true)
    val falsee = BooleanLiteral(false)
    val cond = Equals(p, truee)

    rewriter.addRewriteRule(RewriteRule("If_P", Seq(cond), iteExpr, e1,10))
    rewriter.addRewriteRule(RewriteRule("If_Not_P", Seq(Not(cond)), iteExpr, e2, 10))
    rewriter.addRewriteRule(RewriteRule("Equal_ID", Seq(), Equals(e1,e1), truee, 10))
    rewriter.addRewriteRule(RewriteRule("Equal_True", Seq(Equals(e1, e2)), Equals(e1,e2), truee, 10))
    rewriter.addRewriteRule(RewriteRule("Not_Equal_False", Seq(Not(Equals(e1, e2))), Not(Equals(e1,e2)), truee,10))
    rewriter.addRewriteRule(RewriteRule("Not_Equal_False", Seq(Equals(e1, e2)), Not(Equals(e1,e2)), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Imply_Local_Assumtion", Seq(Implies(e1,Equals(e2, rve2))), Implies(e1,e2), Implies(e1, rve2), 10))
    // rewriter.addRewriteRule(RewriteRule("If_Strong_Cong", Seq(Equals(p, rvp), Implies(cond,Equals(e1, rve1)), Implies(Not(cond),Equals(e2, rve2))), IfExpr(p, e1,e2), IfExpr(rvp, rve1, rve2), 10))

    rewriter.addRewriteRule(RewriteRule("Int_GreaterThan", Seq(GreaterThan(n1, n2)), GreaterThan(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_GreaterThan", Seq(Not(GreaterThan(n1, n2))), GreaterThan(n1,n2), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Int_LessThan", Seq(LessThan(n1, n2)), LessThan(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_LessThan", Seq(Not(LessThan(n1, n2))), LessThan(n1,n2), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Int_LessEqual", Seq(LessEquals(n1, n2)), LessEquals(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_GreaterEqual", Seq(GreaterEquals(n1, n2)), GreaterEquals(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_LessEqual", Seq(Not(LessEquals(n1, n2))), LessEquals(n1,n2), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_Greaterqual", Seq(Not(GreaterEquals(n1, n2))), GreaterEquals(n1,n2), falsee,10))
  }

  val m: MutableMap[Identifier, RewriteVariable] = MutableMap.empty

  def convert2Pattern(e: Expr, s: Set[Variable] = Set()): Expr = {

    def toRewriteVariable(x: Variable): RewriteVariable = {
      val Variable(id) = x
      // I don't really sure if we can use the Identifier, let create new one ;)
      RewriteVariable(FreshIdentifier(id.toString).setType(x.getType))
    }

    def convert2Pattern_rec(expr: Expr, s: Set[Variable]): Expr = expr match {
      case v @ Variable(id) if s.contains(v) => v

      case Variable(id) if m.contains(id) => {
        m(id)
      }

      case v @ Variable(id) => {
        val rl = toRewriteVariable(v)
        m += (id -> rl)
        rl
      }

      case UnaryOperator(t, recons) => {
        recons(convert2Pattern_rec(t,s)).setType(expr.getType)
      }

      case BinaryOperator(t, y, recons) => {
        val i1 = convert2Pattern_rec(t, s)
        val i2 = convert2Pattern_rec(y, s)

        // println(" i1 i2 " + i1 + " : " + i2)
        recons(i1, i2).setType(expr.getType)
      }

      case n @ NAryOperator(args, recons) => {
        recons(args.map(ag => convert2Pattern_rec(ag, s))).setType(expr.getType)
      }

      case t @ _ => t
    }

    convert2Pattern_rec(e, s)
  }

  def createRuleWithDisableVars(e1: Expr, e2: Expr, s: Set[Variable], w: Int) = {
    m.clear()
    RewriteRule("Rule_Disable_Vars", Seq(), convert2Pattern(e1, s), convert2Pattern(e2, s), w)
  }


  def createFunctionRewriteRules(fd: FunDef, prog: Program): Seq[RewriteRule] = {
      // for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2)) {
      // println(funDef.id)
    // Reset our map
    m.clear()
    if (fd.body.isDefined) {
      val Some(imp1) = fd.body
      val imp = simplifyLets(imp1)
      // println(imp)
      // println(funDef.args)
      val fn = fd.id.toString     // function name
      val lstArgs = fd.args.map(arg => { val VarDecl(v, ty) = arg; convert2Pattern(Variable(v).setType(ty)) }).toSeq
      val fi = FunctionInvocation(fd, lstArgs)
      val s0 = imp match { 
        case MatchExpr(_, _) => {
          def travelMatch(ex: Expr, c: Int, conds: Seq[Expr]): Seq[RewriteRule] = {
            ex match {
              case IfExpr(con, ex1, ex2) => {
                val rn = fn + "_simp" + c.toString
                RewriteRule(rn, con +: conds, fi, ex1, 5) +: travelMatch(ex2, c+1, Not(con) +: conds)
              }
              case _ => Seq( RewriteRule(fn + "_simp" + c.toString, conds, fi, ex, 5) )
            } 
          }
          val ex = convert2Pattern(matchToIfThenElse(imp))
          travelMatch(ex, 1, Seq())
        }

        case _ =>
          if (!prog.isRecursive(fd)) {
            Seq(RewriteRule(fd.id.toString + "_simp",Seq(), fi, convert2Pattern(matchToIfThenElse(imp)),15))
          } else Seq()
      }


      // lemma rewrite rules
      val s1 = if(fd.annotations.contains("simp")) {
        // println(fd)
        val precond = fd.precondition match {
          case Some(pre) => Seq(pre)
          case _         => Seq()
        }

        convert2Pattern(imp) match {
          case Equals(e1, e2) => Seq( RewriteRule(fn + "_simp_lemma", precond, e1, e2, 20) )
          case _ => Seq()
        }
      } else Seq()
      

      s0 ++ s1
    } else Seq()
  }
}
