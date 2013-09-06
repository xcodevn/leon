package leon.solvers.lemmafilter

import z3.scala._
import leon.solvers.z3._
import leon.solvers._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.Common._
import leon.purescala.Definitions._

trait Z3Training {
  /*
   * This is a high-level wrapper for MaSh
   * 
   * By using @depend annotation, we can gets dependencies of properties and use it as input for Machine learning algorithm
   * 
   */
  self: AbstractZ3Solver =>

  /*
   * Doing generate the verification condition of a function
   * We use this VC to get getfure for the function
   * 
   * Note: this function is a copy (and simplify) of Z3Lemma, so if Z3Lemma changes, please change this one too :-)
   * Hmmm, I don't think this function returns a VC, I want it return the body of function (property), So I can unfold it and then extract features
   */
  def genVC(funDef: FunDef): Expr = {
    def getImple() = funDef.implementation match {
      case Some(r) => r
      case _ => Error("Error")
    }

    val fname = funDef.id.name
    val imple = getImple()

    val lemmaBody: Expr = funDef.precondition.map { pre =>
      Implies(pre, imple)
    } getOrElse {
      imple
    }

    matchToIfThenElse(lemmaBody)
  }

  /*
   * Extract features by recursive travel Z3AST
   * Use features which were defined in MaSh paper
   * 
   * TODO: Extend/change features set ...  
   * 
   */
  def getFeatureSet(lst: Seq[Z3AST]): Set[(String, Double)] = {
    /*
     * List of thing have to do in right order:
     *   1. Read MaSh paper to now what feature is!
     *   2. Implement this function as a recursive function which travels set of Z3AST trees
     *   		a. Where can I get an example for traversal ? 
     *              A: z3AST to --->,   from Z3AST functions in AbtractZ3Model ? OK
     *              Anything else related to Z3AST, TreeOps, Trees, might be helpful
     *   
     */
    Set()
  }

  /*
   * Train MaSh by the user annotation (@depend)
   */
  def train(unfold: (Expr, Int) => Seq[Z3AST]) = {
    reporter.warning("FIXME: Remember to unlearn before running any testcase !")
    reporter.warning("FIXME: I don't check if lemma dependencies are correct or not")

    for (funDef <- program.definedFunctions if funDef.annotations.contains("depend")) {
      val funName = funDef.id.name.toString()
      val parents = "FIXME:_Don't_understand_how_to_use_this" // I believe we have a way to use this function to improve our filter
        												      // but now, I even also don't know how to use it in the right way
      val features = getFeatureSet(unfold(genVC(funDef), 2))

      val deps = funDef.dependencies match {
        case Some(dep) => dep
        case None => Set[String]()
      }
      
      mash.mash.learn(funName, parents, features, deps)
    }

    /*
     * We use mash API (learn, unlearn, ...) for this training process
     *
     */
    /*
    mash.learn("ROOT", "", Set(), Set())
    mash.learn("First_Lemma", "ROOT", Set(("F1", 2.0), ("F2", 10.0)), Set[String]())
    mash.learn("Second_Lemma", "First_Lemma", Set(("F1", 2.0)), Set[String]("First_Lemma"))
  */

  }

}
