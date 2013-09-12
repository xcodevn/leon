import scala.language.postfixOps
import leon.Annotations._
import leon.Utils._

object Reverse {
  sealed abstract class List
  case class Nil ()extends List
  case class Cons(head: Int, tail: List) extends List
  
  def app(l1: List, l2: List): List = l1 match {
    case Nil() => l2
    case Cons(h, t) => Cons(h, app(t, l2))
  }
  
  def rev(l: List): List = l match {
    case Nil() => Nil()
    case Cons(h, t) => app(rev(t), Cons(h, Nil()))
  }

  @lemma
  @induct
  def appnil(l: List) = { app(l, Nil() ) == l } holds

  @lemma
  @induct
  def app_assoc(l1: List, l2: List, l3: List) = { app(l1, app(l2, l3)) == app( app(l1, l2), l3) } holds

  def nthodd(n: Int): Int = 2*n - 1
  def sumnodd(n: Int):Int = if (n == 1) 1 else nthodd(n) + sumnodd(n-1)

  @lemma
  def odd_sum_lemma(n: Int): Boolean = {
    sumnodd(7) == 7*7
  } holds

  @lemma
  @induct
  def rev_app(l1: List, l2: List) = {
    rev(app(l1, l2) ) == app(rev(l2), rev(l1) )
  } holds

}
