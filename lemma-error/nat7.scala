import leon.Annotations._
import leon.Utils._

object Nat {
  sealed abstract class Nat
  case class Zero() extends Nat
  case class Succ(num: Nat) extends Nat

  def plus(a: Nat, b: Nat): Nat = a match {
    case Zero()   => b
    case Succ(a1) => Succ(plus(a1, b))
  }

  def sub(a: Nat, b: Nat): Nat = if (a == b) Zero() else a match {
    case Zero()          => b
    case Succ(a1)   => Succ(sub(a1, b))
  }

  def isOdd(n: Nat): Boolean = n match {
    case Zero()      => false
    case Succ(n1)   => ! isOdd(n1)
  }

  def isEven(n: Nat) = !isOdd(n)

  @lemma
  def sumEven_lemma1(n1: Nat, n2: Nat): Boolean = {
    require(isEven(n1) && isEven(n2))
    n1 match {
      case Zero() => true
      case Succ(Succ(n10)) => sumEven_lemma1(n10, n2)
    }
  } ensuring {res => res && isEven(plus(n1,n2))}
  
  @lemma
  def sumEven_lemma(n1: Nat, n2: Nat): Boolean  ={
    require(isEven(n1) && isEven(n2))
    sumEven_lemma1(n1,n2) && isEven(plus(n1,n2))
  } holds

  @depend("sumEven_lemma")
  def testSUmlemma(n1: Nat, n2: Nat): Boolean = {
    require(isEven(n1) && isEven(n2))
    isEven(plus(n1,n2))
  } holds
    
}

