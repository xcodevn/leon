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

object Rules {
  def addDefaultRules(rewriter: Rewriter) {
    val p = Variable(FreshIdentifier("cond")).setType(BooleanType)
    val n1 = Variable(FreshIdentifier("n1")).setType(Int32Type)
    val n2 = Variable(FreshIdentifier("n2")).setType(Int32Type)
    val e1= Variable(FreshIdentifier("e1"))
    val e2= Variable(FreshIdentifier("e2"))
    val rve1= Variable(FreshIdentifier("rve1"))
    val rve2= Variable(FreshIdentifier("rve2"))
    val iteExpr = IfExpr(p, e1, e2)
    val truee = BooleanLiteral(true)
    val falsee = BooleanLiteral(false)
    val cond = Equals(p, truee)

    rewriter.addRewriteRule(RewriteRule("If_P", Seq(cond), iteExpr, e1,10))
    rewriter.addRewriteRule(RewriteRule("If_Not_P", Seq(Not(cond)), iteExpr, e2, 10))
    rewriter.addRewriteRule(RewriteRule("Equal_True", Seq(Equals(e1, e2)), Equals(e1,e2), truee, 10))
    rewriter.addRewriteRule(RewriteRule("Equal_True", Seq(Equals(e1, e2)), Equals(e1,e2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Not_Equal_False", Seq(Not(Equals(e1, e2))), Not(Equals(e1,e2)), truee,10))
    rewriter.addRewriteRule(RewriteRule("Not_Equal_False", Seq(Equals(e1, e2)), Not(Equals(e1,e2)), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Imply_Local_Assumtion", Seq(Equals(e1, rve1), Implies(e1,Equals(e2, rve2))), Implies(e1,e2),
      Implies(e1, rve2),10))

    rewriter.addRewriteRule(RewriteRule("Int_GreaterThan", Seq(GreaterThan(n1, n2)), GreaterThan(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_GreaterThan", Seq(Not(GreaterThan(n1, n2))), GreaterThan(n1,n2), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Int_LessThan", Seq(LessThan(n1, n2)), LessThan(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_LessThan", Seq(Not(LessThan(n1, n2))), LessThan(n1,n2), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Int_LessEqual", Seq(LessEquals(n1, n2)), LessEquals(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_GreaterEqual", Seq(GreaterEquals(n1, n2)), GreaterEquals(n1,n2), truee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_LessEqual", Seq(Not(LessEquals(n1, n2))), LessEquals(n1,n2), falsee,10))
    rewriter.addRewriteRule(RewriteRule("Int_Not_Greaterqual", Seq(Not(GreaterEquals(n1, n2))), GreaterEquals(n1,n2), falsee,10))
  }

  def createFunctionRewriteRules(fd: FunDef, prog: Program): Seq[RewriteRule] = {
      // for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2)) {
      // println(funDef.id)
    if (fd.body.isDefined) {
      val Some(imp) = fd.body
      // println(imp)
      // println(funDef.args)
      val fn = fd.id.toString     // function name
      val lstArgs = fd.args.map(arg => { val VarDecl(v, ty) = arg; Variable(v).setType(ty) }).toSeq
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
          val ex = matchToIfThenElse(imp)
          travelMatch(ex, 1, Seq())
        }

        case _ =>
          if (!prog.isRecursive(fd)) {
            Seq(RewriteRule(fd.id.toString + "_simp",Seq(), fi, matchToIfThenElse(imp),15))
          } else Seq()
      }


      // lemma rewrite rules
      val s1 = if(fd.annotations.contains("lemma")) {
        imp match {
          case Equals(e1, e2) => Seq( RewriteRule(fn + "_simp_lemma", Seq(), e1, e2, 20) )
          case _ => Seq()
        }
      } else Seq()
      

      s0 ++ s1
    } else Seq()
  }

}
