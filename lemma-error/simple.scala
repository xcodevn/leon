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

  def subhundred(x: Int) = x - 100
  def double(x: Int) = subhundred(x)*2 + 200

  def equal_lemma(x: Int): Boolean = { if (x > 0)  double(x+1)  == 2+2*x else true } holds
  def equal_lemma1(x: Int): Boolean = { if (x > 0)  double(double(x+1))  == 4+4*x else true } holds

  @induct
  def appnil_lemma(l: List) = { app(l, Nil() ) == l } holds

  @induct
  def app_assoc_lemma(l1: List, l2: List, l3: List) = { app(l1, app(l2, l3)) == app( app(l1, l2), l3) } holds

  @lemma
  @induct
  def app_rev_lemma(l2: List, l1: List) = {
    app(rev(l1), rev(l2)) == rev(app(l2, l1))
  } holds


  def rev_rev_lemma(l: List):Boolean = {
    l match {
      case Nil() => true
      case Cons(x, xs) => rev_rev_lemma(xs)
                          // rev(app(rev(xs), Cons(x, Nil()))) == app(rev(Cons(x, Nil())), rev(rev(xs)))
                          // l == app(rev(Cons(x, Nil())), rev(rev(xs)))
    }
  } ensuring {res => res && rev(rev(l)) == l}

}

