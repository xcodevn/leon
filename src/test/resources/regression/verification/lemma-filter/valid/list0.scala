import leon.Annotations._
import leon.Utils._

object Reverse {
  sealed abstract class List
  case class Nil extends List
  case class Cons(head: Int, tail: List) extends List
  
  def app(l1: List, l2: List): List = l1 match {
    case Nil() => l2
    case Cons(h, t) => Cons(h, app(t, l2))
  }
  
  def rev(l: List): List = l match {
    case Nil() => Nil()
    case Cons(h, t) => app(rev(t), Cons(h, Nil()))
  }

  @induct
  def appnil(l: List) = { app(l, Nil() ) == l } holds

  @induct
  def app_assoc(l1: List, l2: List, l3: List) = { app(l1, app(l2, l3)) == app( app(l1, l2), l3) } holds

  def rev_rev_rec(x: Int, xs: List): Boolean = { 
    app(rev(Cons(x, Nil())), rev(rev(xs)))  == Cons(x, rev(rev(xs)))
  } holds
}
