package leon.solvers.lemmafilter.MaLe

import leon._
import z3.scala._
import leon.solvers.z3._
import leon.solvers._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.Common._
import purescala.Extractors._
import leon.purescala.Definitions._
import scala.collection.mutable.MutableList
import leon.solvers.rewriter._
import scala.collection.JavaConverters._


class MaLeFilter {
  var male = new MaLe()

  def loadData(fileName: String) = {
    male.loadData(fileName)
  }

  def getFeatureList(ex: Expr): Seq[String] = {
    val lst: MutableList[String] = new MutableList()

    def get1LFeature(tree: Expr): Option[String] = tree match {
      case FunctionInvocation(fd, args) => Some(fd.id.toString)
      case CaseClass(ccd, _)            => Some(ccd.id.toString)
      case BooleanLiteral(v)            => Some("CONST_" + v.toString)
      case IntLiteral(v)                => Some("CONST_" + v.toString)
      case _                            => None
    }

    def rec(tree: Expr) : Unit = {
      val s1 = get1LFeature(tree)
      if (s1 != None) lst += s1.get
      tree match {
        case FunctionInvocation(fd, args) => {
          val lst1 = ( for (subtree <- args) yield { rec(subtree); get1LFeature(subtree) } ) filter (x => x != None)
          if (lst1.size > 0) {
            val ft = fd.id.toString + "(%s)".format(lst1.map(x => x.get) mkString (","))
            lst += ft
          } else {}
        }

        case UnaryOperator(t, recons) => rec(t)

        case BinaryOperator(t, y, recons) => { rec(t); rec(y) }

        case NAryOperator(args, recons) => for (st <- args) rec(st)
        case _ => 
      }
    }
    rec(ex)
    lst.distinct
  }

  def getPr (rn: String, fts: Seq[String]): Double = {
    male.classify(rn, fts.asJava)
  }

  def training(d: List[(Expr, List[RewriteRule])], lstRR: List[RewriteRule]) = {
    val lst: MutableList[String] = new MutableList()
    val rules = lstRR map { x => x.name }
    val egs =  ( for ( (ex, lr) <- d ) yield {
      val ft = getFeatureList(ex)
      lst ++= ft
      val newlr = lr map { x => x.name } 
      new Example(ft.asJava, newlr.asJava)
    } )

    val fts = lst.distinct
    male.training(rules.asJava, fts.asJava, egs.asJava)
    male.writeOutFile("ml.dat")
  }

  def writeOut(file: String) = {
    male.writeOutFile(file)
  }

}
