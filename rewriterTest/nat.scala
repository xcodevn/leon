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
  
  @lemma
  def sum_lemma(n: Nat): Int = {
    require (n != Zero())
    n match {
      case Zero() => 1
      case Succ(n1) => 10
    }
  } ensuring {res => res > 9 }

  @lemma
  @induct
  def plus_zero_lemma(n: Nat): Boolean = {
    plus(n, Zero()) == n
  } holds

  @lemma
  def zero_plus_lemma(n: Nat): Boolean = {
    plus(Zero(), n) == n
  } holds

}
