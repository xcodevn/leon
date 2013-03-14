package leon
package lemmas

import purescala.Definitions._
import purescala.TypeTrees._
import purescala.Trees._

object LemmaDiscoveryPhase extends LeonPhase[Program,Program] {
  val name = "Lemma Discovery"
  val description = "Automagically discover lemmas about program functions"

  private lazy val lemmaPost : Expr = ResultVariable().setType(BooleanType)

  def run(ctx : LeonContext)(program : Program) : Program = {
    import ctx.reporter

    reporter.info("Looking for lemmas...")

    for(funDef <- program.definedFunctions if funDef.annotations.contains("lemma")) {
      reporter.info(" - found : [%s]".format(funDef.id.name))
      if(!(funDef.returnType == BooleanType)) {
        reporter.error("Function [%s] is marked as a lemma but is not a predicate.".format(funDef.id.name))
      } else if(!funDef.hasPostcondition) {
        reporter.error("Function [%s] is marked as a lemma but does not have a postcondition.".format(funDef.id.name))
      } else if(funDef.getPostcondition != lemmaPost) {
        reporter.error("Invalid postcondition for lemma [%s].".format(funDef.id.name))
      }
    }
    
    program 
  }
}
