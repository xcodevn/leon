package leon.solvers.lemmafilter

import leon._
import z3.scala._
import leon.solvers.z3._
import leon.solvers._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.solvers.lemmafilter.mash._

@volatile class MaShFilter (context : LeonContext, prog: Program) extends Filter {
  val name = "MaSh Filter"
  val description = "This filter gets suggestions from MaSh tool for filtering"

  /*
   * Create our own Z3 solver
   * Doing some more stuff for correctly running of the solver (that is the problem of a state machine :[ )
   */
  val fairZ3 = new ExtendedFairZ3Solver(context, prog)

  // create new reporter cause we don't use LeonContext
  // val reporter = new DefaultReporter() ; don't need it anymore ;)

  /*
   * Doing generate the verification condition of a function
   * We use this VC to get getfure for the function
   * 
   * Note: this function is a copy (and simplify) of Z3Lemma, so if Z3Lemma changes, please change this one too :-)
   * Hmmm, I don't think this function returns a VC, I want it return the body of function (property), So I can unfold it and then extract features
   */
  def genVC(funDef: FunDef): Expr = {
    context.reporter.info("FIXME: We need a real VC, not just function's body")
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


    def trim(name: String) = name.split("!")(0)
    
    def get1LFeature(tree: Z3AST): String = {
      fairZ3.z3.getASTKind(tree) match {
        case Z3AppAST(decl, args) =>
          if (fairZ3.isKnownDecl(decl)) {
            trim(decl.getName.toString)
          } else {
            import Z3DeclKind._
            fairZ3.z3.getDeclKind(decl) match {
              case OpTrue   => "const_true" // println("new constant TRUE")
              case OpFalse  => "const_false" // println("new constant FALSE")
              case Other    => trim(decl.getName.toString)
              case _        => "" // Empty
            }
          }

        case Z3NumeralAST(Some(v)) => "const_%d".format(v)
       
        case _ => "" // Empty
      }
    }

    /* Until now, we only yield set of strings, need improvement in future for weigth of these string */
    def rec(tree: Z3AST):Set[String] = {
      val s1 = get1LFeature(tree)
      val c2:(Set[String], String) = fairZ3.z3.getASTKind(tree) match {
        case Z3AppAST(decl, args) => 
          ( {for (subtree <- args) yield { rec(subtree) } }.flatten.toSet, 
            {val seq =  for (subtree <- args) yield { get1LFeature(subtree) }
                 seq.filter(s => s.length > 0).mkString(",")})
        case _ => (Set[String]() , "")
      }
      c2 match {
        case (s2, para) => 
          if (para.length > 0) Set(s1) ++ s2 ++ { if (s1.length > 0) Set("%s(%s)".format(s1, para)) else Set() }
          else Set(s1) ++ s2 
      }
    }
    
    /* Now, the momment for return set of feature with (equal, now) weight :-) */
    { for (tree <- lst) yield { rec(tree) } }.flatten.filter(s=> s.length > 0).map(s => (s, 1.0)).toSet    
  }

  /*
   * Train MaSh by the user annotation (@depend)
   */
  def train() = {
    MaSh.unlearn
    // reporter.warning("FIXME: Remember to unlearn before running any testcase !")
    // reporter.warning("FIXME: I don't check if lemma dependencies are correct or not")

    // MaSh.learn("First_Lemma", "", Set(("F1", 2.0), ("F2", 10.0)), Set[String]())
    // MaSh.learn("Second_Lemma", "First_Lemma", Set(("F1", 2.0)), Set[String]("First_Lemma"))
    // reporter.info("Result: " + MaSh.query("Third_Lemma", "Second_Lemma", Set (("F1", 10.0), ("F2", 10.0))))

    val funs = fairZ3.program.definedFunctions.filter(fun => fun.annotations.contains("depend") || fun.annotations.contains("lemma")).toList.sortWith((fd1, fd2) => fd1 < fd2)


    funs.foldLeft("")( (parents, funDef) => {
        val funName = funDef.id.name.toString()

        // I believe we have a way to use this function to improve our filter
        // but now, I even also don't know how to use it in the right way
        // val parents = "FIXME:_Don't_understand_how_to_use_this" 
        val features = getFeatureSet(fairZ3.unfold(genVC(funDef), 1))
        context.reporter.info("Congrats. Below is our set of features of " + funName + "() :\n["+features.mkString(",\n") + "]\n")

        val deps = funDef.dependencies match {
          case Some(dep) =>
            val SetLemmaName = fairZ3.program.definedFunctions.filter(f => LemmaTools.isTrueLemma(f)).map(_.id.name.toString()).toSet
            for (d <- dep) {
              if (!SetLemmaName.contains(d))
                context.reporter.error("%s is NOT a real lemma".format(d))
            }
            dep.filter(d => SetLemmaName.contains(d))
          case None => Set[String]()
        }
        
        MaSh.learn(funName, parents, features, deps)
        funName
    })

  }

  /* 
   * Both conj and expressions in m (a map) should be un-fold before come here
   * We don't handle unfolding procedure, this a way to keep the consitency, modularity, blah blah properties for Leon system
   * FairZ3Solver should be the only place we keep state variables, I have a strong believe that priciple will help us have a better system
   * Just believe in ME :-)
   */
  def filter(conj: Expr, m: Map[FunDef, Expr], num_lemmas: Int = 2): Seq[FunDef] = {
    /* 
     * This function doing like a proxy (if you know what proxy is), it fowards all filter request to MaSh wrapper with a little
     * modification
     *
     */
    
    // Get feature from an expression may be a general function of Z3 Solver itself :|
    // We need some useful function from Z3 :|, How can I do this thing without Z3 :| 
    // Create new Z3 solver for my purpose, yeah !
    //
    val features = getFeatureSet(fairZ3.unfold(conj, 1))
    
    val parents = m.keySet.toList.sortWith( (fd1,fd2) => fd2 < fd1).head.id.name.toString
    
    val suggestions = MaSh.query("We_need_a_name_for_it", parents, features, Set(), num_lemmas)
    val names = suggestions.map(  a => a match { case (b,c) => b} )

    m.keySet.filter(f => names.contains(f.id.name.toString)).toSeq
  }

}
