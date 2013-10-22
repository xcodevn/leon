package leon
package solvers.princess

import scala.collection.mutable.{ Map => MutableMap }
import leon.solvers._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.Common.Identifier
import leon.purescala.Common.FreshIdentifier
import leon.termination.TerminationChecker
import leon.termination.SimpleTerminationChecker
import leon.evaluators.Evaluator
import leon.evaluators.CodeGenEvaluator
import leon.evaluators.DefaultEvaluator
import ap.parser._
import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.preds.Predicate
import leon.evaluators.EvaluationResults

object TestDebug {
  var debug_on = false

  def apply(label: String, msg: String) {
    debug(label, msg)
  }

  def debug(label: String, msg: String = "empty") {
    if (debug_on) {
      if (label.startsWith("\n"))
        println("\n[DEBUG]" + label.replace("\n", "") + msg)
      else if (label.equals("[NODEBUG]"))
        println(msg)
      else
        println("[DEBUG]" + label + msg)
    }
  }
}

class PrincessSolver(val context : LeonContext, val program: Program)
  extends Solver
    with TimeoutAssumptionSolver
    with LeonComponent {

  val name = "Princess"
  val description = "Princess Solver"
  
  protected var interrupted = false;

  override def interrupt() { interrupted = true}
  override def getUnsatCore: Set[leon.purescala.Trees.Expr] = Set()
  override def recoverInterrupt() { interrupted = false}
  override def free() = {prover = null}
  override def innerCheckAssumptions(assumptions: Set[leon.purescala.Trees.Expr]): Option[Boolean] = None
  override  def innerCheck: Option[Boolean] = None
  override val definedOptions: Set[LeonOptionDef] = Set(
    LeonFlagOptionDef("checkmodels", "--checkmodels", "Double-check counter-examples with evaluator"),
    LeonFlagOptionDef("princess", "--princess", "Use prover Princess"),
    LeonValueOptionDef("princesstimeout", "--princesstimeout", "Set timeout in 1 second"),
    LeonValueOptionDef("unrolling", "--unrolling", "Set unrolling number"),
    LeonFlagOptionDef("onlyprove", "--onlyprove", "Only prove the correctness, don't find the counter example"),
    LeonFlagOptionDef("debug", "--debug", "Set debug mode"))
    
  val reporter: Reporter = context.reporter

  var prover: SimpleAPI = null
  var allConstraints: Seq[IExpression] = Seq()

  var unrollingBank: PrincessUnrollingBank = null

  //SimpleAPI(enableAssert = true, dumpSMT = true, smtDumpBasename = "princess_debug")
  //val prover = SimpleAPI.spawnWithAssertions

  val varMap: MutableMap[Identifier, ITerm] = MutableMap.empty
  val reverseVarMap: MutableMap[ITerm, Identifier] = MutableMap.empty
  val boolVarMap: MutableMap[Identifier, IFormula] = MutableMap.empty
  val reverseBoolVarMap: MutableMap[IFormula, Identifier] = MutableMap.empty

  val functionMap: MutableMap[FunDef, IFunction] = MutableMap.empty
  val boolFuncMap: MutableMap[FunDef, Predicate] = MutableMap.empty
  val fieldSelectorMap: MutableMap[String, IFunction] = MutableMap.empty
  val adtTestersMap: MutableMap[CaseClassDef, Predicate] = MutableMap.empty
  val adtConstructorsMap: MutableMap[CaseClassDef, IFunction] = MutableMap.empty
  val typeMap: MutableMap[TypeTree, IFunction] = MutableMap.empty
  val preDefinedOperationMap: MutableMap[(String, Int), IFunction] = MutableMap.empty
  var emptySet: IFunction = null
  var emptySetTerm: ITerm = null
  var unionFun: IFunction = null
  var intersectFun: IFunction = null
  var diffFun: IFunction = null
  var divisible: IFunction = null

  // What wouldn't we do to avoid defining vars?
  val (feelingLucky, checkModels, useCodeGen, evalGroundApps, unrollUnsatCores, usePrincess, timeout, unrollingNumber, onlyProve) = locally {
    var lucky = false
    var check = false
    var codegen = false
    var evalground = false
    var unrollUnsatCores = false
    var usePrincess = false
    var timeout = 60
    var unrollingNumber = 0
    var onlyProve = false

    TestDebug.debug_on = false

    for (opt <- context.options) opt match {
      case LeonFlagOption("checkmodels", v) => check = v
      case LeonFlagOption("feelinglucky", v) => lucky = v
      case LeonFlagOption("codegen", v) => codegen = v
      case LeonFlagOption("evalground", v) => evalground = v
      case LeonFlagOption("fairz3:unrollcores", v) => unrollUnsatCores = v
      case LeonFlagOption("princess", v) => usePrincess = v
      case LeonFlagOption("debug", v) => TestDebug.debug_on = v
      case LeonFlagOption("onlyprove", v) => onlyProve = v

      case LeonValueOption("princesstimeout", value) => timeout = value.toInt
      case LeonValueOption("unrolling", value) => unrollingNumber = value.toInt
      case _ =>
    }

    (lucky, check, codegen, evalground, unrollUnsatCores, usePrincess, timeout, unrollingNumber, onlyProve)
  }

  private var evaluator: Evaluator = null
  def getEvaluator: Evaluator = evaluator

  private var terminator: TerminationChecker = null
  def getTerminator: TerminationChecker = terminator

  private var freeVarsInVC = Set[Identifier]()
  private var frameExpressions = List[List[Expr]](Nil)

  var foundDefinitiveAnswer = false
  var definitiveAnswer: Option[Boolean] = None
  var definitiveModel: Map[Identifier, Expr] = Map.empty
  var definitiveCore: Set[Expr] = Set.empty

  def getModel = definitiveModel

  def resetAllVarMap() {
    varMap.clear
    reverseVarMap.clear
    boolVarMap.clear
    reverseBoolVarMap.clear

    functionMap.clear
    boolFuncMap.clear
    fieldSelectorMap.clear
    adtTestersMap.clear
    adtConstructorsMap.clear
    typeMap.clear
    preDefinedOperationMap.clear
  }

  def resetProver() {
    prover = SimpleAPI(enableAssert = true, dumpSMT = true, smtDumpBasename = "princess_debug", tightFunctionScopes = false)
    allConstraints = Seq()
    unrollingBank = new PrincessUnrollingBank(this, reporter)
    freeVarsInVC = Set()
    frameExpressions = List[List[Expr]](Nil)
    emptySet = prover.createFunction("EmptySet", 1)
    emptySetTerm = IFunApp(emptySet, Seq(prover.createConstant))
    unionFun = prover.createFunction("union", 2)
    intersectFun = prover.createFunction("intersect", 2)
    diffFun = prover.createFunction("diff", 2)
    divisible = prover.createFunction("divisible", 2)
  }

  // helper function to create nested universal formula: forall x, y, z, ... f([x, y, z])
  def createForAllFormula(numOfForAllVar: Int, listForAll: Seq[ITerm], f: Seq[ITerm] => IFormula): IFormula = {
    if (numOfForAllVar <= 0)
      f(listForAll)
    else
      IExpression.all(x => createForAllFormula(numOfForAllVar - 1, listForAll :+ x, f))
  }

  // helper function to create first universal and then exists formula: forall x, exists y, z, ... f([x, y, z])
  def createForAllAndExistFormula(numOfForAllVar: Int, listForAll: Seq[ITerm], f: Seq[ITerm] => IFormula): IFormula = {
    if (numOfForAllVar <= 0)
      f(listForAll)
    else if (listForAll.isEmpty)
      IExpression.all(x => createForAllAndExistFormula(numOfForAllVar - 1, listForAll :+ x, f))
    else
      IExpression.ex(x => createForAllAndExistFormula(numOfForAllVar - 1, listForAll :+ x, f))
  }

  def extractArithmeticAxioms(): Seq[IFormula] = {
    val multiplyOp = this.getOperation("times", 2)
    val divOp = this.getOperation("division", 2)

    //forall x. times(x, 0) === 0
    val zeroMul = IExpression.all(x => {
      val LHS = IFunApp(multiplyOp, Seq(x, 0))
      IExpression.trig(LHS === 0, LHS)
    })

    //forall x. times(x, 1) === x
    val oneMul = IExpression.all(x => {
      val LHS = IFunApp(multiplyOp, Seq(x, 1))
      IExpression.trig(LHS === x, LHS)
    })

    //forall x, y. times(x, y) === times(y, x)
    val commutativeMul = createForAllFormula(2, Seq(), listForAll => {
      val x = listForAll.head
      val y = listForAll.tail.head
      val LHS = IFunApp(multiplyOp, Seq(x, y))
      val RHS = IFunApp(multiplyOp, Seq(y, x))
      IExpression.trig(LHS === RHS, LHS)
    })

    //forall x, y, z[lhs, rhs]. times(x, timearitys(y, z)) === times(times(x, y), z)
    val associativeMul = createForAllFormula(3, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val timesXY = IFunApp(multiplyOp, Seq(x, y))
      val timesYZ = IFunApp(multiplyOp, Seq(y, z))
      val timesXYZ = IFunApp(multiplyOp, Seq(x, timesYZ))
      val timesXYZ_2 = IFunApp(multiplyOp, Seq(timesXY, z))
      IExpression.trig(timesXYZ === timesXYZ_2, timesXYZ, timesXYZ_2)
    })

    //forall x, y, z. times(x, y+z) === times(x, y) + times(x, z)
    val distributiveMul = createForAllFormula(3, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val timesXY = IFunApp(multiplyOp, Seq(x, y))
      val timesXZ = IFunApp(multiplyOp, Seq(x, z))
      val LHS = IFunApp(multiplyOp, Seq(x, y + z))
      val RHS = timesXY + timesXZ
      IExpression.trig(LHS === RHS, LHS)
    })

    //forall x, y, z. z > 0 ==> times(x, z) < times(y, z)
    val inequalityMul = createForAllFormula(3, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val timesXZ = IFunApp(multiplyOp, Seq(x, z))
      val timesYZ = IFunApp(multiplyOp, Seq(y, z))
      IExpression.trig((z > 0 & x < y) ==> timesXZ < timesYZ, timesXZ, timesYZ)
    })

    val divisibility = createForAllFormula(2, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val divYX = IFunApp(divOp, Seq(y, x))
      val timesX = IFunApp(multiplyOp, Seq(divYX, x))
      val LHS = (x === y | (x < y & (timesX === y)))
      val RHS = (IFunApp(divisible, Seq(y, x)) === 1)
      IExpression.trig(LHS <=> RHS, divYX)
    })
    val divisibleAxiom1 = IExpression.all(x => IFunApp(divisible, Seq(x, x)) === 1)
    val divisibleAxiom2 = IExpression.all(x => IExpression.all(y => {
      val divXY = IFunApp(divisible, Seq(x, y))
      IExpression.trig(x < y ==> (divXY === 0), divXY)
    }))
    val divisibleAxiom3 = IExpression.all(x => IExpression.all(y => {
      val divXY = IFunApp(divisible, Seq(x, y))
      val divXY2 = IFunApp(divisible, Seq(x - y, y))
      IExpression.trig(x > y ==> (divXY === divXY2), divXY)
    }))

    Seq(divisibility, divisibleAxiom1, divisibleAxiom2, divisibleAxiom3)
    //Seq(zeroMul, oneMul, commutativeMul, /*associativeMul,distributiveMul,*/ inequalityMul, divisibility, divisibleAxiom1,divisibleAxiom2, divisibleAxiom3)
  }

  def extractAxiomsAboutSetTheory(): Seq[IFormula] = {
    assert(emptySetTerm != null)
    assert(unionFun != null)
    assert(intersectFun != null)

    val unionWithEmptySet = IExpression.all(anyTerm => {
      val unionTerm = IFunApp(unionFun, Seq(emptySetTerm, anyTerm))
      IExpression.trig(unionTerm === anyTerm, unionTerm)
    })

    val unionEqualToEmptySet = createForAllFormula(2, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val unionTerm = IFunApp(unionFun, Seq(x, y))
      IExpression.trig(unionTerm === emptySetTerm ==> (x === emptySetTerm & y === emptySetTerm), unionTerm, emptySetTerm)
    })

    // the set with at least 1 elements is not an empty set
    val setWithAtLeastOneElem = createForAllFormula(3, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val setWithElem = prover.store(x, y, 1)
      IExpression.trig(z === setWithElem ==> (z =/= emptySetTerm), setWithElem)
    })

    val commutativeUnion = createForAllFormula(2, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val unionTerm1 = IFunApp(unionFun, Seq(x, y))
      val unionTerm2 = IFunApp(unionFun, Seq(y, x))
      IExpression.trig(unionTerm1 === unionTerm2, unionTerm1)
    })

    val strongerCommutativeUnion = createForAllFormula(3, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val setTerm = prover.store(emptySetTerm, x, y)
      val unionTerm1 = IFunApp(unionFun, Seq(setTerm, z))
      val unionTerm2 = IFunApp(unionFun, Seq(z, setTerm))
      IExpression.trig(unionTerm1 === unionTerm2, unionTerm1)
    })

    val associativeUnion = createForAllFormula(3, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val XY = IFunApp(unionFun, Seq(x, y))
      val YZ = IFunApp(unionFun, Seq(y, z))
      val XYZ = IFunApp(unionFun, Seq(x, YZ))
      val XYZ_2 = IFunApp(unionFun, Seq(XY, z))
      IExpression.trig(XYZ === XYZ_2, XYZ, XYZ_2)
    })

    val complexUnion = createForAllFormula(4, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val z = listForAll(2)
      val t = listForAll(3)
      val xy = IFunApp(unionFun, Seq(x, y))
      val xyz = IFunApp(unionFun, Seq(xy, z))
      val xyzt = IFunApp(unionFun, Seq(xyz, t))
      val yz = IFunApp(unionFun, Seq(y, z))
      val xt = IFunApp(unionFun, Seq(x, t))
      val yzxt = IFunApp(unionFun, Seq(yz, xt))
      IExpression.trig(xyzt === yzxt, xyzt, yzxt)
    })

    val membershipOfEmptySet = IExpression.all(anyTerm => {
      val selectTerm = prover.select(emptySetTerm, anyTerm)
      IExpression.trig(selectTerm === 0, selectTerm)
    })

    val selectOfUnion = createForAllFormula(5, Seq(), listForAll => {
      val x = listForAll(0)
      val y = listForAll(1)
      val anyTerm = listForAll(2)
      val valueUnion = listForAll(3)
      val valueSelectX = listForAll(4)
      val unionTerm = IFunApp(unionFun, Seq(x, y))
      val selectTerm = prover.select(unionTerm, anyTerm)
      val selectX = prover.select(x, anyTerm)
      IExpression.trig((valueUnion === selectTerm & valueSelectX === selectX) ==> (valueUnion === valueSelectX), selectTerm)
    }) &
      createForAllFormula(5, Seq(), listForAll => {
        val x = listForAll(0)
        val y = listForAll(1)
        val anyTerm = listForAll(2)
        val valueUnion = listForAll(3)
        val valueSelectY = listForAll(4)
        val unionTerm = IFunApp(unionFun, Seq(x, y))
        val selectTerm = prover.select(unionTerm, anyTerm)
        val selectY = prover.select(y, anyTerm)
        IExpression.trig((valueUnion === selectTerm & valueSelectY === selectY) ==> (valueUnion === valueSelectY), selectTerm)
      })

    Seq(unionWithEmptySet, unionEqualToEmptySet, setWithAtLeastOneElem, complexUnion, commutativeUnion, associativeUnion, membershipOfEmptySet, selectOfUnion)
  }

  def extractAxiomsFromADTs(): Seq[IFormula] = {
    val axioms =
      for ((abstrCls, caseClasses) <- program.algebraicDataTypes) yield {
        // example with ADT: List -> Cons, Triple, Nil

        // testerForAbstrAxioms = forall x: List. isCons(x) | isTriple(x) | isNil(x)
        val abstrVarFun = getTypeMap(AbstractClassType(abstrCls))
        val testerForAbstrAxioms =
          IExpression.all(obj => {
            val objMap = IFunApp(abstrVarFun, Seq(obj))
            val allTesterFormula =
              for (caseDef <- caseClasses) yield {
                val testerPred = getAdtTester(caseDef)
                IAtom(testerPred, Seq(objMap))
              }
            IExpression.trig(allTesterFormula.reduceRight((a, b: IFormula) => b | a), objMap)
          })

        // testerForCaseDefAxioms = forall x: Cons. isCons(x),  forall x: Triple. isTriple(x),  forall x: Nil. isNil(x)
        val testerForCaseDefAxioms =
          for (caseDef <- caseClasses) yield {
            val testerPred = getAdtTester(caseDef)
            val caseVarFun = getTypeMap(CaseClassType(caseDef))
            IExpression.all(obj => {
              val objMap = IFunApp(caseVarFun, Seq(obj))
              val tester = IAtom(testerPred, Seq(objMap))
              IExpression.trig(tester, objMap)
            })
          }

        // constructorAxioms = 
        //    + forall x:{Cons, List}, y, z. x = Cons(y, z) -> isCons(x)
        //    + forall x:{Triple, List}, y, z. x = Triple(y, z) -> isTriple(x)
        //    + forall x:{Nil, List}. x = Nil -> isNil(x)
        //    + forall x:{Cons, List}, isCons(x) -> exists y,z. x = Cons(y, z)
        //    + forall x:{Triple, List}, isTriple(x) -> exists y,z. x = Triple(y, z)
        //    + forall x:{Nil, List}. isNil(x) -> x = Nil
        val constructorAxioms =
          (for (caseDef <- caseClasses) yield {
            val constructorFun = getAdtConstructor(caseDef)
            val testerPred = getAdtTester(caseDef)
            val abstrVarFun = getTypeMap(AbstractClassType(abstrCls))
            val caseVarFun = getTypeMap(CaseClassType(caseDef))

            val formulaForAbstr =
              createForAllFormula(constructorFun.arity + 1, Seq(), listForAll => {
                assert(constructorFun.arity + 1 == listForAll.size)
                val x = IFunApp(abstrVarFun, Seq(listForAll.head))
                val constrF = mappingAdtConstructor(caseDef, CaseClassType(caseDef), listForAll.tail)
                val testerF = IAtom(testerPred, Seq(x))
                IExpression.trig((x === constrF) ==> testerF, constrF, x)
              }) &
                createForAllAndExistFormula(constructorFun.arity + 1, Seq(), listForAll => {
                  assert(constructorFun.arity + 1 == listForAll.size)
                  val x = IFunApp(abstrVarFun, Seq(listForAll.head))
                  val constrF = mappingAdtConstructor(caseDef, CaseClassType(caseDef), listForAll.tail)
                  val testerF = IAtom(testerPred, Seq(x))
                  IExpression.trig(testerF ==> (x === constrF), constrF, x)
                })

            val formulaForCaseDef =
              createForAllFormula(constructorFun.arity + 1, Seq(), listForAll => {
                assert(constructorFun.arity + 1 == listForAll.size)
                val x = IFunApp(caseVarFun, Seq(listForAll.head))
                val constrF = mappingAdtConstructor(caseDef, CaseClassType(caseDef), listForAll.tail)
                val testerF = IAtom(testerPred, Seq(x))
                IExpression.trig((x === constrF) ==> testerF, constrF, x)
              }) &
                createForAllAndExistFormula(constructorFun.arity + 1, Seq(), listForAll => {
                  assert(constructorFun.arity + 1 == listForAll.size)
                  val x = IFunApp(caseVarFun, Seq(listForAll.head))
                  val constrF = mappingAdtConstructor(caseDef, CaseClassType(caseDef), listForAll.tail)
                  val testerF = IAtom(testerPred, Seq(x))
                  IExpression.trig(testerF ==> (x === constrF), constrF, x)
                })
            Seq(formulaForAbstr, formulaForCaseDef)
          }).flatten

        // diffForCaseDefAxioms = 
        //     + forall x: Cons. isCons(x) <-> !isTriple(x) && !isNil(x)
        //     + forall x: List. isCons(x) <-> !isTriple(x) && !isNil(x)
        //     + forall x: Triple. isTriple(x) <-> !isCons(x) && !isNil(x)
        //     + forall x: List. isTriple(x) <-> !isCons(x) && !isNil(x)
        //     + forall x: Nil. isNil(x) <-> !isCons(x) && !isTriple(x)
        //     + forall x: List. isNil(x) <-> !isCons(x) && !isTriple(x)
        def allDiffCaseClasses(allDiff: Seq[CaseClassDef], obj: ITerm): IFormula = {
          val allTesterFormula =
            for (caseDef <- allDiff) yield {
              val testerPred = getAdtTester(caseDef)
              !IAtom(testerPred, Seq(obj))
            }
          allTesterFormula.reduceRight((a, b: IFormula) => b & a)
        }
        val diffForCaseDefAxioms =
          (for (caseDef <- caseClasses) yield {
            val testerPred = getAdtTester(caseDef)
            val abstrVarFun = getTypeMap(AbstractClassType(abstrCls))
            val caseVarFun = getTypeMap(CaseClassType(caseDef))

            val otherCaseDef = caseClasses.diff(Seq(caseDef))
            if (otherCaseDef.isEmpty) {
              val formulaForAbstr =
                IExpression.all(obj => {
                  val objMap = IFunApp(abstrVarFun, Seq(obj))
                  IExpression.trig(IAtom(testerPred, Seq(objMap)), objMap)
                })
              Seq(formulaForAbstr)
            } else {
              val formulaForCaseDef =
                IExpression.all(obj => {
                  val objMap = IFunApp(caseVarFun, Seq(obj))
                  val tester = IAtom(testerPred, Seq(objMap))
                  IExpression.trig(tester <=> allDiffCaseClasses(otherCaseDef, objMap), objMap)
                })
              val formulaForAbstr =
                IExpression.all(obj => {
                  val objMap = IFunApp(abstrVarFun, Seq(obj))
                  val tester = IAtom(testerPred, Seq(objMap))
                  IExpression.trig(tester <=> allDiffCaseClasses(otherCaseDef, objMap), objMap)
                })
              Seq(formulaForAbstr, formulaForCaseDef)
            }
          }).flatten

        // example with each caseDef: Const(head: Int, tail: List)
        // forall n, obj, h, t [tailOfConst]. n = tailOfConst(obj) & obj = Const(h, t) -> n = t

        val fieldSelectorAxiom =
          (for (caseDef <- caseClasses) yield {
            val constructorFun = getAdtConstructor(caseDef)
            /*
            for ((selector, index) <- caseDef.allIdentifiers.zipWithIndex) yield {
              createForAllFormula(constructorFun.arity + 2, Seq(), listForAll => {
                val n = listForAll.head
                val obj = listForAll.tail.head
                val args = listForAll.tail.tail
                val constructorTerm = mappingAdtConstructor(caseDef, CaseClassType(caseDef), args)
                val selectorTerm = mappingFieldSelector(caseDef, selector, Seq(obj))
                IExpression.trig((n === selectorTerm & obj === constructorTerm) ==> (n === args(index)), selectorTerm, constructorTerm)
              })
            }
            */
            println("caseDef debug:\n" + caseDef)
            List()
          }).flatten

        testerForAbstrAxioms +: (testerForCaseDefAxioms ++ constructorAxioms ++ diffForCaseDefAxioms ++ fieldSelectorAxiom)
      }
    axioms.flatten.toSeq
  }

  def printAllMap() {
    println("\nvarMap = \n" + varMap.mkString("\n"))
    println("\nboolVarMap = \n" + boolVarMap.mkString("\n"))
    println("\nfunctionMap = \n" + functionMap.mkString("\n"))
    println("\nfieldSelectorMap = \n" + fieldSelectorMap.mkString("\n"))
    println("\nadtTestersMap = \n" + adtTestersMap.mkString("\n"))
    println("\nadtConstructorsMap = \n" + adtConstructorsMap.mkString("\n"))

  }

  def createFreshMapping(tpe: TypeTree): IExpression =
    tpe match {
      case BooleanType => prover.createBooleanVariable
      case Int32Type => prover.createConstant
      case other => IFunApp(getTypeMap(other), Seq(prover.createConstant))
    }

  def lookupOrCreate(id: Identifier): IExpression =
    varMap.getOrElse(id, boolVarMap.getOrElse(id,
      id.getType match {
        case BooleanType => {
          val pred = prover.createBooleanVariable(id.uniqueName)
          boolVarMap += (id -> pred)
          reverseBoolVarMap += (pred -> id)
          pred
        }
        case Int32Type => {
          val c = prover.createConstant(id.uniqueName)
          varMap += (id -> c)
          reverseVarMap += (c -> id)
          c
        }
        case other => {
          val c = IFunApp(getTypeMap(other), Seq(prover.createConstant(id.uniqueName)))
          varMap += (id -> c)
          reverseVarMap += (c -> id)
          c
        }
      }))

  def idToPrincessId(id: Identifier): IExpression = lookupOrCreate(id)

  def getFunSym(fun: FunDef): IFunction = functionMap.getOrElse(fun, {
    val newSym = prover.createFunction(fun.id.name, fun.args.size)
    functionMap += fun -> newSym
    newSym
  })

  def getPredSym(fun: FunDef): Predicate = boolFuncMap.getOrElse(fun, {
    val newSym = prover.createRelation(fun.id.name, fun.args.size)
    boolFuncMap += fun -> newSym
    newSym
  })

  def getFieldSelector(classDef: CaseClassDef, id: Identifier): IFunction = {
    val searchName = id.name + "Of" + classDef.id.name
    fieldSelectorMap.getOrElse(searchName, {
      val newSym = prover.createFunction(searchName, 1)
      fieldSelectorMap += searchName -> newSym
      newSym
    })
  }

  def mappingFieldSelector(classDef: CaseClassDef, selector: Identifier, args: Seq[ITerm]): IFunApp = {
    val funSymbol = getFieldSelector(classDef, selector)
    val tpeSelector = selector.getType
    val tpeSym = getTypeMap(tpeSelector)
    tpeSelector match {
      case Int32Type => IFunApp(funSymbol, args)
      case _ => IFunApp(tpeSym, Seq(IFunApp(funSymbol, args)))
    }
  }

  def getAdtTester(classDef: CaseClassDef): Predicate = adtTestersMap.getOrElse(classDef, {
    val newSym = prover.createRelation("is" + classDef.id.name, 1)
    adtTestersMap += classDef -> newSym
    newSym
  })

  def getAdtConstructor(classDef: CaseClassDef): IFunction = adtConstructorsMap.getOrElse(classDef, {
    val newSym = prover.createFunction(classDef.id.name.toUpperCase, classDef.fields.size)
    adtConstructorsMap += classDef -> newSym
    newSym
  })

  def mappingAdtConstructor(classDef: CaseClassDef, typeConstructor: TypeTree, args: Seq[ITerm]): IFunApp = {
    val adtSym = getAdtConstructor(classDef)
    val tpeSym = getTypeMap(typeConstructor)
    IFunApp(tpeSym, Seq(IFunApp(adtSym, args)))
  }

  def getTypeMap(tpe: TypeTree): IFunction = typeMap.getOrElse(tpe, {
    val newSym = prover.createFunction("Type" + tpe.toString, 1)
    typeMap += tpe -> newSym
    newSym
  })

  def getOperation(op: String, arity: Int): IFunction = preDefinedOperationMap.getOrElse((op, arity), {
    val newSym = prover.createFunction(op, arity)
    preDefinedOperationMap += (op, arity) -> newSym
    newSym
  })

  def getNewSolver: IncrementalSolver = null

  def solve(vc: Expr): Option[Boolean] = {
    Some(true)
  }

/*
  override def solveSAT(vc: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    if (!usePrincess) {
      (None, Map.empty)
    } else
      try {
        this.resetAllVarMap
        this.resetProver
        val arithAxioms = this.extractArithmeticAxioms()
        val adtAxioms = this.extractAxiomsFromADTs()
        val setAxioms = this.extractAxiomsAboutSetTheory()

        TestDebug("[NODEBUG]", "=======================================================================================")
        TestDebug("[NODEBUG]", "================================ PRINCESS SOLVER RUNNING ==============================")
        TestDebug("[NODEBUG]", "=======================================================================================")
        TestDebug("[Princess][solveSat]", "vc = " + vc)
        //TestDebug("[Princess][solveSat]", "princess_formula = " + toPrincessFormula(vc))
        //TestDebug("[Princess][SolveSat]", " - Create all axioms for Algebraic Data Type:\n" + adtAxioms.mkString("\n"))

        this.addConstraints(arithAxioms)
        this.addConstraints(adtAxioms)
        this.addConstraints(setAxioms)
        this.assertCnstr(vc)

        val abc = this.boolVarMap.toList.filter(_._1.name.contains("errorValue"))
        for ((_, b) <- abc) {
          this.addConstraints(Seq(!b))
        }

        val res = this.fairCheck(Set())

        TestDebug("[NODEBUG]", "=======================================================================================")
        TestDebug("[NODEBUG]", "==================================== PRINCESS STOP ====================================")
        TestDebug("[NODEBUG]", "=======================================================================================")

        prover.shutDown
        (res, this.getModel)
      } catch {
        case CantTranslateException(msg) =>
          reporter.error(msg)
          (None, Map.empty)
        /*
        case e =>
          reporter.error(" - Got this exception:")
          reporter.error(e)
          (None, Map.empty)
        */
      }
  }
*/

  def push() {
    prover.push
    unrollingBank.push
    frameExpressions = Nil :: frameExpressions
  }

  def pop() {
    val lvl = 1
    prover.pop
    unrollingBank.pop(lvl)
    frameExpressions = frameExpressions.drop(lvl)
  }

  def assertCnstr(expression: Expr) {
    freeVarsInVC ++= variablesOf(expression)
    frameExpressions = (expression :: frameExpressions.head) :: frameExpressions.tail
    val newClauses = unrollingBank.scanForNewTemplates(expression)
    this.addConstraints(newClauses)
  }

  def addAssumptions(exprs: Seq[IExpression]) {
    TestDebug("[AddAssumption]", "")
    for (e <- exprs) {
      TestDebug("[NODEBUG]", "adding " + e)
      prover !! e.asInstanceOf[IFormula]
    }
  }

  def addConstraints(exprs: Seq[IExpression]) {
    allConstraints = allConstraints ++ exprs
    TestDebug("[AddConstraints]", "")
    for (e <- exprs) {
      val newFormula = e
      /*
        substitutePrincessFormula(e, Seq(), Seq(), {
          case IFunApp(fun, args) =>
            val timesOp = getOperation("times", 2)
            if (timesOp == fun) {
              try {
                args.head * args.tail.head
              } catch {
                case e: IllegalArgumentException => IFunApp(fun, args)
              }
            } else
              IFunApp(fun, args)
          case e => e
        })
      */
      TestDebug("[NODEBUG]", "adding " + newFormula)
      prover !! newFormula.asInstanceOf[IFormula]
    }
  }

  private def validateModel(model: Map[Identifier, Expr], formula: Expr, silenceErrors: Boolean): Boolean = {
    if (!interrupted) {
      val evalResult = evaluator.eval(formula, model)

      evalResult match {
        case EvaluationResults.Successful(BooleanLiteral(true)) =>
          reporter.info("- Model validated.")
          true

        case EvaluationResults.Successful(BooleanLiteral(false)) =>
          reporter.info("- Invalid model.")
          false

        case EvaluationResults.RuntimeError(msg) =>
          reporter.info("- Model leads to runtime error.")
          false

        case EvaluationResults.EvaluatorError(msg) =>
          if (silenceErrors) {
            reporter.info("- Model leads to evaluator error: " + msg)
          } else {
            reporter.warning("Something went wrong. While evaluating the model, we got this : " + msg)
          }
          false

      }
    } else {
      false
    }
  }

  def findCounterExample(): Map[Identifier, Expr] = {
    def printWarningIfCantGetModel(v: Identifier) {
      reporter.warning("Can't get model for this variable: " + v + " -> get any value")
      reporter.warning("--> should double-check counter-examples with evaluator [--checkmodels]")
    }

    def findModel(v: Identifier, mapVar: IExpression): Expr = v.getType match {
      case BooleanType =>
        try {
          prover.evalPartial(mapVar.asInstanceOf[IFormula]) match {
            case Some(res) => BooleanLiteral(res)
            case None =>
              printWarningIfCantGetModel(v)
              BooleanLiteral(true)
          }
        } catch {
          case e: AssertionError =>
            printWarningIfCantGetModel(v)
            IntLiteral(0)
        }
      case Int32Type =>
        try {
          prover.evalPartial(mapVar.asInstanceOf[ITerm]) match {
            case Some(res) => IntLiteral(res.intValue)
            case None =>
              printWarningIfCantGetModel(v)
              IntLiteral(0)
          }
        } catch {
          case e: AssertionError =>
            printWarningIfCantGetModel(v)
            IntLiteral(0)
        }
      case AbstractClassType(absClssDef) => {
        assert(mapVar.isInstanceOf[ITerm])
        val term = mapVar.asInstanceOf[ITerm]
        val allCaseClssDef = program.algebraicDataTypes(absClssDef)

        // select all possible type for term
        val possibleCaseDefs = allCaseClssDef.filter(caseDef => {
          val tester = getAdtTester(caseDef)
          val testerFormula = IAtom(tester, Seq(term))

          reporter.info("checking the shape of " + term + ": " + testerFormula)

          /*
          prover.eval(testerFormula) 
          */

          prover.push
          this.addConstraints(Seq(testerFormula))
          val res = prover.???
          prover.pop
          res match {
            case ProverStatus.Unsat =>
              reporter.info("false"); false
            case ProverStatus.Sat => reporter.info("true"); true
          }

        })

        def chooseSuitableCaseDef(allCaseDef: Seq[CaseClassDef]): CaseClassDef =
          allCaseDef.reduce((e1, e2) => 
            /*if (e1.allIdentifiers.size < e2.allIdentifiers.size) e1 else e2 */
            e1
          )

        // if cannot find any type
        if (possibleCaseDefs.isEmpty) {
          printWarningIfCantGetModel(v)
          val smallestCaseDef = chooseSuitableCaseDef(allCaseClssDef)
          /*val args = smallestCaseDef.allIdentifiers.toSeq*/
          val args = Seq(smallestCaseDef.id)
          val modelForArgs: Seq[Expr] = args.map(arg => findModel(arg, createFreshMapping(arg.getType)))
          CaseClass(smallestCaseDef, modelForArgs)
        } else {
          //  then choose the best type if it is not empty
          reporter.info("==> found possible ADTs: " + possibleCaseDefs.map(_.id))
          val caseDef = chooseSuitableCaseDef(possibleCaseDefs)
          /*val args = caseDef.allIdentifiers.toSeq*/
          val args = Seq(caseDef.id)

          /*
          First method
          val mappingArgs = args.map(e => mappingFieldSelector(caseDef, e, Seq(term)))
          val modelForArgs: Seq[Expr] = (args zip mappingArgs).map(elem => findModel(elem._1, elem._2))
          */

          //Another method to find model
          val mappingArgs = args.map(e => createFreshMapping(e.getType).asInstanceOf[ITerm])
          val formula = term === mappingAdtConstructor(caseDef, CaseClassType(caseDef), mappingArgs)
          prover.push
          addConstraints(Seq(formula))
          val tmp = prover.???
          assert(tmp == ProverStatus.Sat)
          val modelForArgs: Seq[Expr] = (args zip mappingArgs).map(elem => findModel(elem._1, elem._2))
          prover.pop

          CaseClass(caseDef, modelForArgs)
        }
      }
      case CaseClassType(caseClssDef) => {
        assert(mapVar.isInstanceOf[ITerm])
        val term = mapVar.asInstanceOf[ITerm]
        /*val args = caseClssDef.allIdentifiers.toSeq*/
        val args = Seq(caseClssDef.id)
        
        val mappingArgs = args.map(e => createFreshMapping(e.getType).asInstanceOf[ITerm])

        val formula = term === mappingAdtConstructor(caseClssDef, CaseClassType(caseClssDef), mappingArgs)
        prover.push
        addConstraints(Seq(formula))
        val tmp = prover.???
        assert(tmp == ProverStatus.Sat)
        val modelForArgs: Seq[Expr] = (args zip mappingArgs).map(elem => findModel(elem._1, elem._2))
        prover.pop

        CaseClass(caseClssDef, modelForArgs)
      }
      case _ => {
        reporter.warning("not implemented with [" + v.getType.getClass() + "]")
        IntLiteral(-1)
      }
    }

    val mapVars = freeVarsInVC.map(v => (v, lookupOrCreate(v)))
    val model =
      (for ((v, mapVar) <- mapVars) yield {
        val res = findModel(v, mapVar)
        val mappingResult = toPrincessFormula(res)
        assert(mappingResult.isDefined)
        mapVar match {
          case f: IFormula =>
            assert(mappingResult.get.isInstanceOf[IFormula])
            val f2 = mappingResult.get.asInstanceOf[IFormula]
            prover !! (f <=> f2)
          case t: ITerm =>

            assert(mappingResult.get.isInstanceOf[ITerm])
            val term = mappingResult.get.asInstanceOf[ITerm]
            prover !! (t === term)
        }
        val checkAgain = prover.???
        assert(checkAgain == ProverStatus.Sat)

        v -> res
      }).toMap
    model
  }

  def runProver(p: SimpleAPI, timeout: Int = 0): Option[SimpleAPI.ProverStatus.Value] = {
    if (timeout == 0)
      Some(p.???)
    else {
      p.checkSat(false)

      p.getStatus(timeout) match {
        case ProverStatus.Running => None
        case ProverStatus.Unsat => Some(ProverStatus.Unsat)
        case ProverStatus.Sat => Some(ProverStatus.Sat)
      }
    }
  }

  def fairCheck(assumptions: Set[Expr]): Option[Boolean] = {
    val totalTime = new Stopwatch().start
    val luckyTime = new Stopwatch()
    val princessTime = new Stopwatch()
    val findModelTime = new Stopwatch()
    val unrollingTime = new Stopwatch()
    val unlockingTime = new Stopwatch()

    foundDefinitiveAnswer = false

    def entireFormula = And(assumptions.toSeq ++ frameExpressions.flatten)

    def foundAnswer(answer: Option[Boolean], model: Map[Identifier, Expr] = Map.empty, core: Set[Expr] = Set.empty): Unit = {
      foundDefinitiveAnswer = true
      definitiveAnswer = answer
      definitiveModel = model
      definitiveCore = core
    }

    // these are the optional sequence of assumption literals
    val assumptionsAsPrincess: Seq[IExpression] = assumptions.flatMap(toPrincessFormula(_)).toSeq

    var unrollingCount = 0
    while (!foundDefinitiveAnswer && !interrupted) {
      reporter.info(" - Running Princess search...")

      TestDebug("[Princess][fairCheck]", "Unroll.  Assumptions:\n" + unrollingBank.currentPrincessBlockers.mkString("  &&  "))
      //TestDebug("[Princess][fairCheck]", " - Searching in all constraints:\n" + allConstraints.mkString("\n"))

      prover.push
      val res =
        if (!onlyProve || !unrollingBank.canUnroll) {
          princessTime.start
          this.addAssumptions(assumptionsAsPrincess ++ unrollingBank.currentPrincessBlockers)
          val tmp = prover.???
          princessTime.stop
          reporter.info(" - Finished search with blocked literals")
          tmp
        } else {
          reporter.warning("Don't prove with blocked literals")
          ProverStatus.Unsat
        }

      res match {
        case ProverStatus.Sat => {
          reporter.error(" - Result is SAT, trying to find a model ...")
          findModelTime.start
          try {
            val model = findCounterExample()
            findModelTime.stop
            prover.pop
            if (this.checkModels) {
              val isValid = validateModel(model, entireFormula, silenceErrors = false)
              if (isValid) {
                foundAnswer(Some(true), model)
              } else {
                reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
                reporter.error(model)
                foundAnswer(None, model)
              }
            } else {
              reporter.error(" - Found a model:\n" + model.mkString("\n"))
              foundAnswer(Some(true), model)
            }
          } catch {
            case e: AssertionError =>
              reporter.error("Cannot find the counter-example for this VCs.")
              foundAnswer(None)
          }
        }

        case ProverStatus.Unsat if !unrollingBank.canUnroll => {
          prover.pop
          reporter.error(" - UNSAT and cannot unroll ==> VALID")
          foundAnswer(Some(false))
        }

        case ProverStatus.Unsat => {
          if (!interrupted) {
            if (this.feelingLucky) {
              // we need the model to perform the additional test
              reporter.info(" - Running search without blocked literals (w/ lucky test)")
            } else {
              reporter.info(" - Running search without blocked literals (w/o lucky test)")
            }

            prover.pop

            if (!TestDebug.debug_on) {
              if (unrollingCount >= unrollingNumber) {
                princessTime.start
                prover.push
                this.addAssumptions(assumptionsAsPrincess)
                val res2 = runProver(prover, timeout * 1000)
                princessTime.stop

                res2 match {
                  case Some(ProverStatus.Unsat) =>
                    reporter.error("UNSAT WITHOUT Blockers ==> VALID")
                    foundAnswer(Some(false))
                    prover.pop

                  case Some(ProverStatus.Sat) =>
                    reporter.warning("SAT WITHOUT Blockers")
                    prover.pop

                  case None =>
                    val doubleCheck = prover.stop
                    doubleCheck match {
                      case ProverStatus.Unsat =>
                        reporter.error("UNSAT (2) WITHOUT Blockers ==> VALID")
                        foundAnswer(Some(false))
                      case ProverStatus.Sat =>
                        reporter.warning("SAT (2) WITHOUT Blockers")
                      case ProverStatus.Unknown =>
                        reporter.warning("TIMEOUT in " + timeout + " second")
                    }
                    prover.pop
                    
                  case _ =>
                    reporter.fatalError("Unexpected case here !!!")
                }
              } else {
                reporter.warning("Don't prove at this time, just unrolling")
              }
            } else {
              /*
                if (unrollingBank.currentPrincessBlockers.size >=fairCheck 15 && unrollingBank.currentPrincessBlockers.size <= 20) {
                  val b0 = boolVarMap.values.find(_.toString().equals("b0")).get
                  val b1 = boolVarMap.values.find(_.toString().equals("b1")).get
                  val b2 = boolVarMap.values.find(_.toString().equals("b2")).get
                  val b3 = boolVarMap.values.find(_.toString().equals("b3")).get
                  val b4 = boolVarMap.values.find(_.toString().equals("b4")).get
                  val b5 = boolVarMap.values.find(_.toString().equals("b5")).get
                  val b14 = boolVarMap.values.find(_.toString().equals("b14")).get
                  val b15 = boolVarMap.values.find(_.toString().equals("b15")).get
                  val b16 = boolVarMap.values.find(_.toString().equals("b16")).get
                  val b17 = boolVarMap.values.find(_.toString().equals("b17")).get
                  val lt0 = varMap.find({ case (id, _) => id.uniqueName.contains("lt0") }).get._2
                  val e0 = varMap.find({ case (id, _) => id.uniqueName.contains("e0") }).get._2
                  val isNil = adtTestersMap.find({ case (casedef, _) => casedef.id.name.contains("Nil") }).get._2
                  val isCons = adtTestersMap.find({ case (casedef, _) => casedef.id.name.contains("Cons") }).get._2
                  val rearOfQueue = this.fieldSelectorMap.find(_._1.contains("rear")).get._2
                  val lt0 = varMap.find(_._1.uniqueName.contains("lt0")).get._2
				  val Nils = adtConstructorsMap.find(_._1.id.uniqueName.contains("Nil")).get._2
			      val isNil = adtTestersMap.find({ case (casedef, _) => casedef.id.name.contains("Nil") }).get._2
                }
                */

              var pairOfBools: Seq[(IFormula, IFormula)] = Seq()
              val setOfBoolVarFromStart =
                allConstraints.filter(f => f match {
                  case IBinFormula(IBinJunctor.Or, INot(IAtom(start, Seq())), IBinFormula(IBinJunctor.Or, f1 @ IAtom(b1, Seq()), f2 @ IAtom(b2, Seq()))) if start.name.contains("start") =>
                    val check = allConstraints.exists({
                      case IBinFormula(IBinJunctor.Or, INot(IAtom(start, Seq())), IBinFormula(IBinJunctor.Or, INot(IAtom(b3, Seq())), INot(IAtom(b4, Seq())))) if start.name.contains("start") && b1.toString.equals(b3.toString) && b2.toString.equals(b4.toString) => true
                      case _ => false
                    })
                    if (check)
                      pairOfBools = (f1, f2) +: pairOfBools
                    check
                  case _ => false
                })

              println("allConstraints.size = " + allConstraints.size)
              println("pairOfBools = \n" + pairOfBools.mkString("\n"))

              var countSat = 0
              var countUnSat = 0
              if (!pairOfBools.isEmpty) {
                val allPairs = pairOfBools.reverse
                val totalLoop = math.pow(2, allPairs.size).toInt

                for (i <- (0 until totalLoop)) {
                  var binary = Integer.toBinaryString(i)
                  while (binary.size < allPairs.size) {
                    binary = "0" + binary
                  }
                  assert(binary.size == allPairs.size)
                  val decision = binary.toCharArray().toSeq
                  val selectedBool = (allPairs zip decision).map(elem => {
                    val ((b1, b2), bit) = elem
                    if (Integer.parseInt(bit.toString) == 0)
                      b1
                    else
                      b2
                  })

                  println("adding " + selectedBool.mkString(" and "))

                  prover.push
                  for (cl <- selectedBool) {
                    prover !! cl
                  }
                  val tmp = prover.???
                  tmp match {
                    case ProverStatus.Unsat => countUnSat += 1
                    case ProverStatus.Sat =>
                      println("############################################################################################################")
                      println("result = " + tmp)
                      println("############################################################################################################")
                      countSat += 1
                    /*
                        prover !! (IFunApp(rearOfQueue, Seq(lt0)) === IFunApp(Nils, Seq()))
                        prover !! (IAtom(isNil, Seq(IFunApp(rearOfQueue, Seq(lt0)))))
                        println(prover.???)
                      
                        var consequences: Seq[IFormula] = Seq()
                        for (idguard <- selectedBool) {
                          println("Guard: " + guard + " ===> ")
                          allConstraints.foreach(f => f match {
                            case IBinFormula(IBinJunctor.Or, INot(IAtom(b, Seq())), cons) if b.name.equals(guard.toString) =>
                              consequences = consequences ++ Seq(cons)
                            case _ => ()
                          })
                          println(consequences.mkString("\n"))
                        }
                        */
                  }
                  prover.pop
                }
                println("Total SAT = " + countSat)
                println("Total UNSAT = " + countUnSat)
                println("############################################################################################################")
              }
              if (countSat > 0) {
                reporter.warning("SAT WITHOUT Blockers")
              } else {
                reporter.error("UNSAT WITHOUT Blockers ==> VALID")
                foundAnswer(Some(false))
              }
            }
          }

          if (interrupted) {
            foundAnswer(None)
          }

          if (!foundDefinitiveAnswer) {
            reporter.info("- We need to keep going.")

            val toRelease = unrollingBank.getPrincessBlockersToUnlock

            reporter.info(" - more unrollings")
            unrollingCount += 1

            for (id <- toRelease) {
              unlockingTime.start
              val newClauses = unrollingBank.unlock(id.asInstanceOf[IFormula])
              unlockingTime.stop

              TestDebug("[NODEBUG]", "\n[" + unrollingCount + "]Unrolling to new clauses (" + newClauses.size + ") for id = " + id + ":\n" + newClauses.mkString("\n"))

              unrollingTime.start
              this.addConstraints(newClauses)
              unrollingTime.stop
            }

            reporter.info(" - finished unrolling")
          }

        } // End res match {case ProverStatus.Unsat => }
      } // End res match {}
    } // End While

    totalTime.stop
    StopwatchCollections.get("FairZ3 Total") += totalTime
    StopwatchCollections.get("FairZ3 Lucky Tests") += luckyTime
    StopwatchCollections.get("FairZ3 Z3") += princessTime
    StopwatchCollections.get("FairZ3 Unrolling") += unrollingTime
    StopwatchCollections.get("FairZ3 Unlocking") += unlockingTime
    StopwatchCollections.get("FairZ3 FindModelTime") += findModelTime

    //reporter.info(" !! DONE !! ")

    if (interrupted) {
      None
    } else {
      definitiveAnswer
    }
  }

  def substitutePrincessFormula(expr: IExpression, from: Seq[IExpression], to: Seq[IExpression], f: IExpression => IExpression = { case e => e }): IExpression = {
    def rec(e: IExpression, mapping: Map[IExpression, IExpression]): IExpression =
      mapping.getOrElse(e, e match {
        // IExpression has 2 subclass: ITerm & IFormula

        // Subclass of ITerm
        case IIntLit(_) | IConstant(_) | IVariable(_) => e
        case ITimes(coeff, subterm) =>
          ITimes(coeff, mapping.getOrElse(subterm, rec(subterm, mapping)).asInstanceOf[ITerm])
        case IPlus(term1, term2) =>
          IPlus((mapping.getOrElse(term1, rec(term1, mapping))).asInstanceOf[ITerm], (mapping.getOrElse(term2, rec(term2, mapping))).asInstanceOf[ITerm])
        case IFunApp(fun, args) =>
          val newArgs = args.map(term => (mapping.getOrElse(term, rec(term, mapping))).asInstanceOf[ITerm])
          f(IFunApp(fun, newArgs))
        case ITermITE(cond, left, right) =>
          val newCond = (mapping.getOrElse(cond, rec(cond, mapping))).asInstanceOf[IFormula]
          val newLeft = (mapping.getOrElse(left, rec(left, mapping))).asInstanceOf[ITerm]
          val newRight = (mapping.getOrElse(right, rec(right, mapping))).asInstanceOf[ITerm]
          ITermITE(newCond, newLeft, newRight)
        case IEpsilon(cond) => IEpsilon((mapping.getOrElse(cond, rec(cond, mapping))).asInstanceOf[IFormula])

        // Subclass of IFormula
        case IBoolLit(_) => e
        case INot(f) => INot((mapping.getOrElse(f, rec(f, mapping))).asInstanceOf[IFormula])
        case IBinFormula(op, f1, f2) =>
          val newF1 = (mapping.getOrElse(f1, rec(f1, mapping))).asInstanceOf[IFormula]
          val newF2 = (mapping.getOrElse(f2, rec(f2, mapping))).asInstanceOf[IFormula]
          IBinFormula(op, newF1, newF2)
        case IAtom(pred, args) =>
          // if this is a boolean variable
          if (args.size == 0)
            mapping.getOrElse(e, e)
          else {
            val newArgs = args.map(term => (mapping.getOrElse(term, rec(term, mapping))).asInstanceOf[ITerm])
            IAtom(pred, newArgs)
          }
        case IIntFormula(rel, term) => IIntFormula(rel, (mapping.getOrElse(term, rec(term, mapping))).asInstanceOf[ITerm])
        case IQuantified(quan, f) => IQuantified(quan, (mapping.getOrElse(f, rec(f, mapping))).asInstanceOf[IFormula])
        case IFormulaITE(cond, left, right) =>
          val newCond = (mapping.getOrElse(cond, rec(cond, mapping))).asInstanceOf[IFormula]
          val newLeft = (mapping.getOrElse(left, rec(left, mapping))).asInstanceOf[IFormula]
          val newRight = (mapping.getOrElse(right, rec(right, mapping))).asInstanceOf[IFormula]
          IFormulaITE(newCond, newLeft, newRight)
        case ITrigger(patterns, f) =>
          ITrigger(patterns.map(term => (mapping.getOrElse(term, rec(term, mapping))).asInstanceOf[ITerm]), (mapping.getOrElse(f, rec(f, mapping))).asInstanceOf[IFormula])
        case INamedPart(name, f) => INamedPart(name, (mapping.getOrElse(f, rec(f, mapping))).asInstanceOf[IFormula])
      })

    val mapping = (from zip to).toMap
    rec(expr, mapping)
  }

  case class CantTranslateException(msg: String) extends Exception(msg)

  def toPrincessFormula(expr: Expr): Option[IExpression] = {

    //var fieldSelectorFormulas: Seq[IFormula] = Seq()
    var allLetFormulas: Seq[IFormula] = Seq()
    val selectorCache: MutableMap[(Expr, Identifier), ITerm] = MutableMap.empty

    // the value of ex will be assigned to lhs variable
    def rec(ex: Expr): IExpression = {
      //println("Stacking up call for: " + ex)
      val recResult = (ex match {
        case And(exs) => exs.map(rec(_).asInstanceOf[IFormula]).reduceLeft((acc, e) => acc & e)
        case Or(exs) => exs.map(rec(_).asInstanceOf[IFormula]).reduceLeft((acc, e) => acc | e)
        case Implies(l, r) => rec(l).asInstanceOf[IFormula] ==> rec(r).asInstanceOf[IFormula]
        case Iff(l, r) => rec(l).asInstanceOf[IFormula] <=> rec(r).asInstanceOf[IFormula]
        case Not(e) => !rec(e).asInstanceOf[IFormula]

        case Equals(l, r) => rec(l).asInstanceOf[ITerm] === rec(r).asInstanceOf[ITerm]
        case LessThan(l, r) => rec(l).asInstanceOf[ITerm] < rec(r).asInstanceOf[ITerm]
        case LessEquals(l, r) => rec(l).asInstanceOf[ITerm] <= rec(r).asInstanceOf[ITerm]
        case GreaterThan(l, r) => rec(l).asInstanceOf[ITerm] > rec(r).asInstanceOf[ITerm]
        case GreaterEquals(l, r) => rec(l).asInstanceOf[ITerm] >= rec(r).asInstanceOf[ITerm]

        case Plus(l, r) => rec(l).asInstanceOf[ITerm] + rec(r).asInstanceOf[ITerm]
        case Minus(l, r) => rec(l).asInstanceOf[ITerm] - rec(r).asInstanceOf[ITerm]
        case Times(l, r) =>
          val resultLeft = rec(l).asInstanceOf[ITerm]
          val resultRight = rec(r).asInstanceOf[ITerm]
          try {
            resultLeft * resultRight
          } catch {
            case e: IllegalArgumentException =>
              // unsupported multiply between 2 term which are not constant
              val newOp = getOperation("times", 2)
              IFunApp(newOp, Seq(resultLeft, resultRight))
          }
        case Division(l, r) =>
          val resultLeft = rec(l).asInstanceOf[ITerm]
          val resultRight = rec(r).asInstanceOf[ITerm]
          val newOp = getOperation("division", 2)
          IFunApp(newOp, Seq(resultLeft, resultRight))
        case Modulo(l, r) =>
          val resultLeft = rec(l).asInstanceOf[ITerm]
          val resultRight = rec(r).asInstanceOf[ITerm]
          val newOp = getOperation("modulo", 2)
          IFunApp(newOp, Seq(resultLeft, resultRight))
        case UMinus(e) =>
          -rec(e).asInstanceOf[ITerm]
        case IntLiteral(v) => IIntLit(v)
        case BooleanLiteral(v) => IBoolLit(v)
        case UnitLiteral => throw new CantTranslateException("Unsupported UnitLiteral")

        case v @ Variable(id) => lookupOrCreate(id)

        case ite @ IfExpr(c, t, e) =>
          val cond = rec(c).asInstanceOf[IFormula]
          val thenResult = rec(t)
          val elseResult = rec(e)
          assert(t.getType == e.getType)
          t.getType match {
            case BooleanType => IFormulaITE(cond, thenResult.asInstanceOf[IFormula], elseResult.asInstanceOf[IFormula])
            case _ => ITermITE(cond, thenResult.asInstanceOf[ITerm], elseResult.asInstanceOf[ITerm])
          }
        /*
          (thenResult, elseResult) match {
            case (thenF: IFormula, elseF: IFormula) =>
              IFormulaITE(cond, thenF, elseF)
            case (thenT: ITerm, elseT: ITerm) =>
              if (lhs.isDefined) {
                val lhsSymbol = lookupOrCreate(lhs.get).asInstanceOf[ITerm]
                lhsSymbol === ITermITE(cond, thenT, elseT)
              } else
                ITermITE(cond, thenT, elseT)
            case (thenF: IFormula, elseT: ITerm) =>
              val lhsSymbol = lookupOrCreate(lhs.get).asInstanceOf[ITerm]
              (cond ==> thenF) & (!cond ==> (lhsSymbol === elseT))
            case (thenT: ITerm, elseF: IFormula) =>
              val lhsSymbol = lookupOrCreate(lhs.get).asInstanceOf[ITerm]
              (cond ==> (lhsSymboltoPrincessFormula === thenT)) & (!cond ==> elseF)
          }
*/
        case FunctionInvocation(fd, args) => {
          ex.getType match {
            case BooleanType =>
              val predSymbol = getPredSym(fd)
              val argSymbols = args.map(rec(_).asInstanceOf[ITerm])
              IAtom(predSymbol, argSymbols)
            case Int32Type =>
              val funSymbol = getFunSym(fd)
              val argSymbols = args.map(rec(_).asInstanceOf[ITerm])
              IFunApp(funSymbol, argSymbols)
            case other =>
              val funSymbol = getFunSym(fd)
              val tpeSymbol = getTypeMap(other)
              val argSymbols = args.map(rec(_).asInstanceOf[ITerm])
              IFunApp(tpeSymbol, Seq(IFunApp(funSymbol, argSymbols)))
          }
        }
        case c @ CaseClass(cd, args) => {
          val argSym = args.map(rec(_).asInstanceOf[ITerm])
          mappingAdtConstructor(cd, c.getType, argSym)
        }
        case CaseClassInstanceOf(ccd, e) => {
          val testFun = getAdtTester(ccd)
          val arg = rec(e).asInstanceOf[ITerm]
          IAtom(testFun, Seq(arg))
        }
        case CaseClassSelector(caseDef, caseExpr, selector) => {
          val arg = rec(caseExpr).asInstanceOf[ITerm]
          val selectorTerm = mappingFieldSelector(caseDef, selector, Seq(arg))

          /*
          val constructorFun = getAdtConstructor(caseDef)
          val indexOfSelector = caseDef.allIdentifiers.zipWithIndex.find(elem => elem._1 == selector).get._2
          val fieldSelectorAxiom =
            createForAllFormula(constructorFun.arity + 1, Seq(), listForAll => {
              val n = listForAll.head
              val args = listForAll.tail
              val constructorTerm = mappingAdtConstructor(caseDef, CaseClassType(caseDef), args)

              IExpression.trig((n === selectorTerm & arg === constructorTerm) ==> (n === args(indexOfSelector)), selectorTerm, constructorTerm)
            })
          println("fieldSelectorAxiom = \n" + fieldSelectorAxiom)
          fieldSelectorAxioms = fieldSelectorAxiom +: fieldSelectorAxioms
*/
          selectorTerm
          /*
          selectorCache.getOrElse((caseExpr, selector), {            
            val selectorID = FreshIdentifier(selector.name + "_" + caseDef.id.name, true).setType(ex.getType)
            val selectorTerm = lookupOrCreate(selectorID).asInstanceOf[ITerm]
            fieldSelectorFormulas = (selectorTerm === resultTerm) +: fieldSelectorFormulas
            selectorCache += (caseExpr, selector) -> selectorTerm
            selectorTerm
          })
          */
        }
        case Let(i, e, b) => {
          val newSymbol = lookupOrCreate(i)
          val exprResult = rec(e)
          val newF =
            e.getType match {
              case BooleanType =>
                assert(exprResult.isInstanceOf[IFormula])
                newSymbol.asInstanceOf[IFormula] <=> exprResult.asInstanceOf[IFormula]
              case _ =>
                assert(exprResult.isInstanceOf[ITerm])
                newSymbol.asInstanceOf[ITerm] === exprResult.asInstanceOf[ITerm]
            }
          allLetFormulas = newF +: allLetFormulas
          rec(b)
        }

        case e @ Error(_) => {
          val errorID: Identifier = FreshIdentifier("errorValue", true).setType(e.getType)
          val b = lookupOrCreate(errorID)
          if (b.isInstanceOf[IFormula])
            this.addConstraints(Seq(!b.asInstanceOf[IFormula]))
          b
        }

        case f @ FiniteSet(elems) =>
          elems.foldLeft(emptySetTerm)((setTerm, el) => prover.store(setTerm, rec(el).asInstanceOf[ITerm], 1))

        case SetIntersection(s1, s2) => IFunApp(intersectFun, Seq(rec(s1).asInstanceOf[ITerm], rec(s2).asInstanceOf[ITerm]))
        case SetUnion(s1, s2) => IFunApp(unionFun, Seq(rec(s1).asInstanceOf[ITerm], rec(s2).asInstanceOf[ITerm]))

        case ElementOfSet(e, s) =>
          val elemTerm = rec(e)
          val setTerm = rec(s)
          assert(elemTerm.isInstanceOf[ITerm])
          assert(setTerm.isInstanceOf[ITerm])
          prover.select(setTerm.asInstanceOf[ITerm], elemTerm.asInstanceOf[ITerm]) === 1

        case SetDifference(s1, s2) => IFunApp(diffFun, Seq(rec(s1).asInstanceOf[ITerm], rec(s2).asInstanceOf[ITerm]))

        /*
        case SubsetOf(s1, s2) =>
        case SetCardinality(s) =>
        case SetMin(s) =>
        case SetMax(s) =>
*/
        case _ =>
          throw new CantTranslateException("Can't handle this in translation to Princess: " + ex + " type = " + ex.getClass())

        /*
        case tu @ Tuple(args) => {
          // This call is required, because the Z3 sort may not have been generated yet.
          // If it has, it's just a map lookup and instant return.
          typeToSort(tu.getType)
          val constructor = tupleConstructors(tu.getType)
          constructor(args.map(rec(_, None)): _*)
        }
        case ts @ TupleSelect(tu, i) => {
          // See comment above for similar code.
          typeToSort(tu.getType)
          val selector = tupleSelectors(tu.getType)(i-1)
          selector(rec(tu))
        }

        case Waypoint(_, e) => rec(e, None)

        case SetEquals(s1, s2) => z3.mkEq(rec(s1), rec(s2))
 
        case f @ FiniteMap(elems) => f.getType match {
          case tpe@MapType(fromType, toType) =>
            typeToSort(tpe) //had to add this here because the mapRangeNoneConstructors was not yet constructed...
            val fromSort = typeToSort(fromType)
            val toSort = typeToSort(toType)
            elems.foldLeft(z3.mkConstArray(fromSort, mapRangeNoneConstructors(toType)())){ case (ast, (k,v)) => z3.mkStore(ast, rec(k), mapRangeSomeConstructors(toType)(rec(v))) }
          case errorType => scala.sys.error("Unexpected type for finite map: " + (ex, errorType))
        }
        case mg @ MapGet(m,k) => m.getType match {
          case MapType(fromType, toType) =>
            val selected = z3.mkSelect(rec(m), rec(k))
            mapRangeValueSelectors(toType)(selected)
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case MapUnion(m1,m2) => m1.getType match {
          case MapType(ft, tt) => m2 match {
            case FiniteMap(ss) =>
              ss.foldLeft(rec(m1)){
                case (ast, (k, v)) => z3.mkStore(ast, rec(k), mapRangeSomeConstructors(tt)(rec(v)))
              }
            case _ => scala.sys.error("map updates can only be applied with concrete map instances")
          }
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case MapIsDefinedAt(m,k) => m.getType match {
          case MapType(ft, tt) => z3.mkDistinct(z3.mkSelect(rec(m), rec(k)), mapRangeNoneConstructors(tt)())
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case fill @ ArrayFill(length, default) => {
          val at@ArrayType(base) = fill.getType
          typeToSort(at)
          val cons = arrayTupleCons(at)
          val ar = z3.mkConstArray(typeToSort(base), rec(default))
          val res = cons(ar, rec(length))
          res
        }
        case ArraySelect(a, index) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getArray = arrayTupleSelectorArray(a.getType)
          val res = z3.mkSelect(getArray(ar), rec(index))
          res
        }
        case ArrayUpdated(a, index, newVal) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getArray = arrayTupleSelectorArray(a.getType)
          val getLength = arrayTupleSelectorLength(a.getType)
          val cons = arrayTupleCons(a.getType)
          val store = z3.mkStore(getArray(ar), rec(index), rec(newVal))
          val res = cons(store, getLength(ar))
          res
        }
        case ArrayLength(a) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getLength = arrayTupleSelectorLength(a.getType)
          val res = getLength(ar)
          res
        }
        case Distinct(exs) => z3.mkDistinct(exs.map(rec(_, None)): _*)
  
        case _ => {
          reporter.warning("Can't handle this in translation to Z3: " + ex)
          throw new CantTranslateException
        }
        */
      })
      //println("recResult = " + recResult + "[" + recResult.getClass() + "]")
      recResult
    }

    def conjunction(formulas: Seq[IFormula]): IFormula =
      if (formulas.isEmpty) IBoolLit(true)
      else formulas.reduce((acc, e) => acc & e)

    allLetFormulas = Seq()
    val output = rec(expr)
    val letFormulas = conjunction(allLetFormulas.reverse)
    val finalOutput =
      output match {
        case f: IFormula => Some(letFormulas &&& f)
        case t: ITerm =>
          if (!allLetFormulas.isEmpty)
            TestDebug("[NODEBUG]", "allLetFormulas = \n" + allLetFormulas.mkString("\n"))
          assert(allLetFormulas.isEmpty); Some(t)
      }
    finalOutput
  }
}
