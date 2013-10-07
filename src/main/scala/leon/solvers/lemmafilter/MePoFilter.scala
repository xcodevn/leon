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

class MePoFilter (context : LeonContext, prog: Program) extends Filter {
  val name = "MePo Filter"
  val description = "Filter by using symbolic relevance, we build a symbol pool, we put inside the pool, symbols occurs in our goal and facts which have related with our goal"

  /*
   * Create our own Z3 solver
   * Doing some more stuff for correctly running of the solver (that is the problem of a state machine :[ )
   */
  val fairZ3 = new ExtendedFairZ3Solver(context, prog)

  val NUM_UNFOLD = 1         // We should be change this value
  val CONST_C = 2.4          // We should be change this value
  val CONST_P = 0.6          // We should be change this value
   

  override def finalize() {
    fairZ3.free()
  }

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

  def getSymbolSet(lst: Seq[Z3AST]): Set[String] = {

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

    def getSymbol_rec(tree: Z3AST):Set[String] = {
      val s1 = get1LFeature(tree)
      val s2: Set[String] = fairZ3.z3.getASTKind(tree) match {
        case Z3AppAST(decl, args) =>  args.foldLeft(Set.empty[String])( (set, tree) => set ++ getSymbol_rec(tree) )
        case _ => Set[String]()
      }

      if (s1.length > 0) Set(s1) ++ s2 else s2
    }
    
    lst.foldLeft(Set.empty[String]) ( (set, tree) => set ++ getSymbol_rec(tree) ) 
  }

  def get_clause_mark(rs: Set[String], c: Seq[Z3AST]): Double = {
    val cs = getSymbolSet(c)
    val size_r = (cs & rs).size.toDouble

    context.reporter.info(cs.toString + " has mark " + "%.2f".format(size_r /cs.size) + " in set "  + rs.toString)
    size_r / cs.size
  }

  def get_relevant_clauses(rs: Set[String], t: Set[(FunDef, Seq[Z3AST])], p: Double, num: Int): Set[(FunDef, Seq[Z3AST])] = {
    context.reporter.info("Current MePo status: RS: %s, T: %s, P: %.2f".format(rs.toString, t.toSeq.map(p => {val (fd, ex) = p ; fd.id.name.toString} ), p))
    val rel = t.filter( e => { val (fd, ex) = e; get_clause_mark(rs, ex) >= p } )
    val new_t = t.filterNot( e => { val (fd, ex) = e; get_clause_mark(rs, ex) >= p } )
    if (!rel.isEmpty) {
      val new_p = p + (1  - p) / CONST_C
      val new_rs = rs ++  rel.toSeq.foldLeft ( Set.empty[String] ) ( (set, p) => set ++ { val (fd, ex) = p; getSymbolSet(ex) } )

      context.reporter.info("Added " + rel.map( p => {val (fd, seq) =p; fd.id.name.toString } ).toString + " into relevance set ")

      if (num - rel.size > 0) 
        rel ++ get_relevant_clauses(new_rs, new_t, new_p, num - rel.size)
      else rel
    } else rel
  }

  def filter(conj: Expr, m: Map[FunDef, Expr], num: Int = 2): Seq[FunDef] = {
    val T = m.toSet.map( (p: (FunDef, Expr)) => { val (fd, ex) = p ; (fd, fairZ3.unfold(ex, NUM_UNFOLD)) } )

    get_relevant_clauses( getSymbolSet(fairZ3.unfold(conj, NUM_UNFOLD)), T, CONST_P, num ).toSeq.map( p => { val (fd, ex) = p; fd } )
  }

}
