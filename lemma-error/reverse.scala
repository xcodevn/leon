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

  @lemma @induct
  def appnil_lemma(l: List) = { app(l, Nil() ) == l } holds

  @lemma @induct
  def app_assoc_lemma(l1: List, l2: List, l3: List) = { app(l1, app(l2, l3)) == app( app(l1, l2), l3) } holds

  @lemma @induct
  def app_rev_lemma(l2: List, l1: List) = {
    app(rev(l1), rev(l2)) == rev(app(l2, l1))
  } holds

  @induct
  def revrev_lemma(l: List):Boolean = {
    rev(rev(l)) == l
  } holds

}

