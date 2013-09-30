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


  @lemma @induct @depend() @simp
  def plus_zero_lemma(a: Nat): Boolean = {
    plus(Zero(), a) == a
  } holds

  @lemma @induct @depend()
  def sub_zero_lemma(a: Nat): Boolean = {
    sub(a, Zero()) == a
  } holds

  @lemma @induct @depend() @simp
  def assoc_plus_lemma(a: Nat, b: Nat, c: Nat): Boolean = {
    plus(a, plus(b, c)) == plus(plus(a, b), c)
  } holds
  
  @depend()
  def zero_sub_lemma(a: Nat): Boolean = {
    sub(Zero(), a) == a
  } holds

  def one() = Succ(Zero())

  @lemma @induct @depend() @simp
  def plusOne_lemma1(a: Nat): Boolean = {
    Succ(a) == plus(one(), a)
  } holds

  @lemma @induct @depend() @simp
  def plusOne_lemma2(a: Nat): Boolean = {
    Succ(a) == plus(a, one())
  } holds

  @lemma @induct @depend() @simp
  def plus_lemma(a: Nat, b: Nat, c: Nat): Boolean = {
    require (a == b)
    plus(a, c) == plus(b, c)
  } holds


  @lemma @depend("plusOne_lemma2", "assoc_plus_lemma", "plus_zero_lemma") @induct
  def swap_plus_lemma(a: Nat, b: Nat): Boolean =  {
    plus(a, b) == plus(b, a)
  }  holds

  def isOdd(n: Nat): Boolean = n match {
    case Zero()      => false
    case Succ(n1)   => ! isOdd(n1)
  }

  def isEven(n: Nat) = !isOdd(n)

  def three_odd_lemma1() = {isOdd(int2Nat(8)) } holds
  def three_odd_lemma2() = {isOdd(int2Nat(9)) } holds

  def sub1_lemma() = { 7 == nat2Int(sub(int2Nat(3), int2Nat(4))) } holds
  def sub2_lemma() = { 1 == nat2Int(sub(int2Nat(4), int2Nat(3))) } holds

  @lemma
  @induct
  @depend("plus_zero_lemma")
  def plusZeroEven_lemma(n: Nat): Boolean = {
    require(isEven(n))
    isEven(plus(n, Zero())) && isEven(plus(Zero(), n))
  } holds

  @lemma
  @depend()
  def evenEven_lemma(n1: Nat, n2: Nat): Boolean = {
    require(isEven(n1) && isEven(n2))
    n1 match {
      case Zero()         => true
      case Succ(Succ(n0)) => isEven(n0) && evenEven_lemma(n0, n2)
    }
  } ensuring {res => res && isEven(plus(n1, n2))}

  @lemma
  @induct
  def plusSucc_lemma(n1: Nat, n2: Nat): Boolean = {
    plus(n1, Succ(n2)) == Succ(plus(n1,n2))
  } holds

  @induct
  @lemma 
  def SuccSuccEven_lemma(n: Nat): Boolean = {
    require(isEven(n))
    isEven(Succ(Succ(n)))
  } holds
  
  @depend("evenEven_lemma", "SuccSuccEven_lemma", "plusSucc_lemma")
  def sumOdd_lemma(n1: Nat, n2: Nat): Boolean = {
    require(isOdd(n1) && isOdd(n2))
    (n1,n2) match {
      case (Succ(n10), Succ(n20)) =>  isEven(n10) && isEven(n20) && isEven(plus(n10, n20)) &&
                                      isEven(plus(n10,n20))    // ; I don't know what wrong with this line (sadly :()
                                      //evenEven_lemma(n10,n20) // &&
                                      // plus(Succ(n10), Succ(n20)) == Succ(Succ(plus(n10, n20)))
    }
  } ensuring {res => res && isEven(plus(n1, n2))}

}
