/* Expression compiler correctness.
   Filip Maric and Viktor Kuncak
*/
import leon.Utils._
import leon.Annotations._
import scala.language.postfixOps

object ReverseList {
  sealed abstract class List
  case class Nil() extends List
  case class Cons(head: Int, tail: List) extends List
  
  def app(l1: List, l2: List): List = l1 match {
    case Nil() => l2
    case Cons(h, t) => Cons(h, app(t, l2))
  }
  
  def rec(l: List): List = l match {
    case Nil() => Nil()
    case Cons(h, t) => app(rec(t), Cons(h, Nil()))
  }
  
  def app_nil(l: List): Boolean = { app(l, Nil()) == l } 

  def plus2(x: Int) = { x + 2 }
  
  @depend("app_nil","app_nil2", "app(Nil(),Nil())")
  def run_rec_app_nil(l: List): Boolean = {
    l match {
      case Nil() => app_nil(l)
      case Cons(h, t) => run_rec_app_nil(t)  && app_nil(l)  && Cons(12, l) == Cons(plus2(10), l)
    } 
  } holds
  
}
