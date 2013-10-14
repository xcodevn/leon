/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import collection.mutable.MutableList
import leon.solvers.rewriter._

class ExtendedInductionTactic(reporter: Reporter) extends InductionTactic(reporter) {
  override val description = "Extended induction tactic for suitable functions"
  
  val inductVars: MutableList[Variable] = MutableList()

  private def firstAbsClassDef(args: VarDecls) : Option[(AbstractClassDef, VarDecl)] = {
    val filtered = args.filter(arg =>
      arg.getType match {
        case AbstractClassType(_) => true
        case _ => false
      })
    if (filtered.size == 0) None else (filtered.head.getType match {
      case AbstractClassType(classDef) => Some((classDef, filtered.head))
      case _ => scala.sys.error("This should not happen.")
    })
  } 

  private def selectorsOfParentType(parentType: ClassType, ccd: CaseClassDef, expr: Expr) : Seq[Expr] = {
    val childrenOfSameType = ccd.fields.filter(field => field.getType == parentType)
    for (field <- childrenOfSameType) yield {
      CaseClassSelector(ccd, expr, field.id).setType(parentType)
    }
  }

  def generateInductiveHypothesisRewriteRules(funDef: FunDef) : Seq[RewriteRule] = {
    assert(funDef.body.isDefined)
    firstAbsClassDef(funDef.args) match {
      case Some((classDef, arg)) =>
        val prec = funDef.precondition
        val optPost = funDef.postcondition
        val body = matchToIfThenElse(funDef.body.get)
        val argAsVar = arg.toVariable

        optPost match {
          case None =>
            Seq.empty
          case Some((pid, post)) =>
            val children = classDef.knownChildren
            val rules: Seq[Seq[RewriteRule]] = (for (child <- classDef.knownChildren) yield (child match {
              case ccd @ CaseClassDef(id, prnt, vds) =>
                val selectors = selectorsOfParentType(classDefToClassType(classDef), ccd, argAsVar)
                // if no subtrees of parent type, assert property for base case
                val resFresh = FreshIdentifier("result", true).setType(body.getType)
                val bodyAndPostForArg = Let(resFresh, body, replace(Map(Variable(pid) -> Variable(resFresh)), matchToIfThenElse(post)))
                val withPrec = if (prec.isEmpty) bodyAndPostForArg else Implies(matchToIfThenElse(prec.get), bodyAndPostForArg)

                if (selectors.size == 0) 
                  Seq()
                else {
                  val rs: Seq[Seq[RewriteRule]] = (for (sel <- selectors) yield {
                    val resFresh = FreshIdentifier("result", true).setType(body.getType)
                    inductVars += argAsVar
                    val nb = replace(Map(argAsVar -> sel), body)
                    nb match {
                      case Equals(e1, e2) if !funDef.hasPrecondition => {
                        Seq(Rules.createRuleWithDisableVars(e1, e2, Set(argAsVar), 25))
                      }
                      case _ => Seq()
                    }
                  })
                  rs.flatten
                }
              case _ => Seq()
            }))
            rules.flatten
        }

      case None => {
        reporter.warning("Induction tactic currently supports exactly one argument of abstract class type")
        Seq()
      }
    }
  }
}
