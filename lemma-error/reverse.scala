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

  @lemma
  @induct
  def appnil(l: List) = { app(l, Nil() ) == l } holds

  @lemma
  @induct
  def app_assoc(l1: List, l2: List, l3: List) = { app(l1, app(l2, l3)) == app( app(l1, l2), l3) } holds

  def app_assoc4(l1: List, l2: List, l3: List, l4: List) =  {
    app(app(l1, l2), app(l3, l4)) == app(l1, app(l2, app(l3, l4) ) )
  } holds


  @lemma
  @induct
  def app_rev(l1: List, l2: List) = {
    app(rev(l1), rev(l2)) == rev(app(l2, l1))
  } holds

  def app_rev_rec(l1: List, l2: List): Boolean = {
    l2 match {
      case Nil() => app_rev(l1, l2)
      case Cons(x, xs) =>   app_rev_rec(l1, xs) &&
                            app_rev(l1,l2)

    }
  } holds
 

  def rev_rev(l: List) = {
    rev(rev(l)) == l
  } 

  def rev_rev_rec(l: List):Boolean = {
    l match {
      case Nil() => rev_rev(l)
      case Cons(x, xs) => rev_rev_rec(xs) && 
                          rev_rev(l)
    }
  } holds 

  @lemma
  def rev_rev_lemma(l: List) = { rev_rev_rec(l) && (rev(rev(l)) == l) } holds
}
