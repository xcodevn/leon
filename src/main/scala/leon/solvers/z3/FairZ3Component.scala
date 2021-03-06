/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

trait FairZ3Component extends LeonComponent {
  val name = "Z3-f"
  val description = "Fair Z3 Solver"

  override val definedOptions : Set[LeonOptionDef] = Set(
    LeonFlagOptionDef("evalground",         "--evalground",         "Use evaluator on functions applied to ground arguments"),
    LeonFlagOptionDef("checkmodels",        "--checkmodels",        "Double-check counter-examples with evaluator"),
    LeonFlagOptionDef("feelinglucky",       "--feelinglucky",       "Use evaluator to find counter-examples early"),
    LeonFlagOptionDef("codegen",            "--codegen",            "Use compiled evaluator instead of interpreter"),
    LeonFlagOptionDef("fairz3:unrollcores", "--fairz3:unrollcores", "Use unsat-cores to drive unrolling while remaining fair"),
    LeonFlagOptionDef("lemmas",             "--lemmas",             "Magical lemma mystery train"),
    LeonValueOptionDef("filter",            "--filter=MePo|MaSh",   "Using a filter (MePo or MaSh) for reducing the number of lemmas"),
    LeonValueOptionDef("num-lemmas",        "--num-lemmas=n",       "The filter only get first n return result as lemmas for the proof"))
}
