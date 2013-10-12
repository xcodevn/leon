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

  def nat2Int(n: Nat): Int = n match {
    case Zero() => 0
    case Succ(n1) => 1 + nat2Int(n1)
  }

  def int2Nat(n: Int): Nat = if (n == 0) Zero() else Succ(int2Nat(n-1))
  
  def isEqual(a: Nat, b: Nat): Boolean = a == b
  
  def sum_lemma(): Boolean = {
    // 7 == nat2Int(plus(int2Nat(3), int2Nat(4)))
    Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero()))))))) == plus( Succ(Succ(Succ(Zero()))), Succ(Succ(Succ(Succ(Zero())))))
  } holds


  @lemma @induct @depend()
  def plus_zero_lemma(a: Nat): Boolean = {
    plus(a, Zero()) == a
  } holds

  @lemma @induct @depend()
  def sub_zero_lemma(a: Nat): Boolean = {
    sub(a, Zero()) == a
  } holds

  @lemma @induct @depend()
  def assoc_plus_lemma(a: Nat, b: Nat, c: Nat): Boolean = {
    plus(a, plus(b, c)) == plus(plus(a, b), c)
  } holds
  
  @depend()
  def zero_sub_lemma(a: Nat): Boolean = {
    sub(Zero(), a) == a
  } holds

  def one() = Succ(Zero())

  @lemma @induct @depend()
  def plusOne_lemma1(a: Nat): Boolean = {
    plus(one(), a) == Succ(a)
  } holds

  @lemma @induct @depend()
  def plusOne_lemma2(a: Nat): Boolean = {
    plus(a, one()) == Succ(a)
  } holds

  @lemma @depend()
  def plus_lemma(a: Nat, b: Nat, c: Nat): Boolean = {
    require (a == b)
    plus(a, c) == plus(b, c)
  } holds


  @depend("plusOne_lemma2", "assoc_plus_lemma", "plus_zero_lemma")
  def swap_plus_lemma(a: Nat, b: Nat): Boolean =  {
    a match {
      case Zero()   => true
      case Succ(a1) => swap_plus_lemma(a1, b) && plus(a, b) == plus(b, a)
                       // plus(b, Succ(a1)) == plus(b, plus(one(), a1)) &&
                       // plus(b, plus(one(), a1)) == plus( plus(b, one()), a1 ) &&
                       // plus(b, one()) == Succ(b) 
                       // plus(Succ(b), a1 ) == Succ(plus(b, a1))
    }
  } ensuring { res => res && plus(a, b) == plus(b, a) }

  def isOdd(n: Nat): Boolean = n match {
    case Zero()      => false
    case Succ(n1)   => ! isOdd(n1)
  }

  def isEven(n: Nat) = !isOdd(n)

  def three_odd_lemma1() = {isOdd(int2Nat(8)) } holds
  def three_odd_lemma2() = {isOdd(int2Nat(9)) } holds

  
  @induct
  def sumOdd_lemma(n1: Nat, n2: Nat): Boolean = {
    require(isOdd(n1) && isOdd(n2))
    n1 match {
      case Zero() => true // never happen
      case Succ(n11) => true
    }
  } holds

}
