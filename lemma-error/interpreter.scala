/* Expression compiler correctness.
   Filip Maric and Viktor Kuncak
*/
import leon.Utils._
import leon.Annotations._

object ExpressionCompiler {
  sealed abstract class Sign
  case class NUM(x : Int) extends Sign
  case class PLUS extends Sign

  sealed abstract class List
  case class Cons(head : Sign, tail : List) extends List
  case class Nil() extends List
  def single(x: Sign) = Cons(x, Nil())
  
  sealed abstract class Expr
  case class Num(x: Int) extends Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
 
  def eval(e: Expr) : Int = {
   e match {
     case Num(x) => x
     case Plus(e1, e2) => eval(e1) + eval(e2)
   }
 }
 
 def postfixAcc(e : Expr, acc : List) : List = {
   e match {
     case Num(x) => Cons(NUM(x),acc)
     case Plus(e1, e2) => postfixAcc(e1, postfixAcc(e2, Cons(PLUS(), acc)))
   }
 }
 
 sealed abstract class Stack
 case class Empty extends Stack
 case class Push(i: Int, s: Stack) extends Stack
 
 def run(l:List, s: Stack) : Stack = {
   l match {
     case Nil() => s
     case Cons(NUM(x), ss) => run(ss, Push(x, s))
     case Cons(PLUS(), ss) => s match {
       case Push(a, Push(b, s1)) => run(ss, (Push(a + b, s1)))
       case _ => Empty()
     }
   }
 }

  // note: no 'holds'
 def run_lemma(e: Expr, post: List, stack: Stack) = {
   run(postfixAcc(e, post), stack) == run(post, Push(eval(e), stack))
 }

 def run_lemma1(e: Expr, p: List, s: Stack): Boolean = {
   e match {
     case Num(x) => true
     case Plus(e1,e2) => true
   }
 } ensuring { res => res && run_lemma(e, p, s) }

  // we express induction with generalization using appropriate recursion
 def run_lemma_induct(e: Expr, ss: List, stack: Stack) : Boolean = {
   e match {
     case Num(x) => run_lemma(e, ss, stack)
     case Plus(e1, e2) => run_lemma(e, ss, stack) && 
       run_lemma_induct(e1, postfixAcc(e2, Cons(PLUS(), ss)), stack) &&
       run_lemma_induct(e2, Cons(PLUS(),ss), Push(eval(e1), stack))
   }
 } holds
 // could also write: ensuring(res =>  (res && run_lemma(e, ss, stack)))

 def compilation_correct(e:Expr) = {
    // this is the proof:
   run_lemma_induct(e,Nil(),Empty()) &&
   // this is the statement:
   run(postfixAcc(e,Nil()), Empty()) == Push(eval(e), Empty())
 } holds
 
 /*
 
  // inlining is crucial to knowing that property was proved
  // proof hints are expressed as extra conjuncts
 def test_run_lemma(e: Expr, ss: List, stack: Stack) = {
   // this is the proof:
   run_lemma_induct(e, ss, stack) &&
   // this is the statement:
   run(postfixAcc(e, ss), stack) == run(ss, Push(eval(e), stack))
 } holds
 */
}
