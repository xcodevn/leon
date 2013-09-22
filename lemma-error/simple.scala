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

  @lemma
  def equal_lemma(x: Int): Boolean = { if (x > 0)  double(x+1)  == 2+2*x else true } holds
  def equal_lemma1(x: Int): Boolean = { if (x > 0)  double(double(x+1))  == 4+4*x else true } holds

  @lemma
  @induct
  def appnil_lemma(l: List) = { app(l, Nil() ) == l } holds

  @lemma
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
      case Cons(x, xs) => rev_rev_lemma(xs) &&
                          rev(app(rev(xs), Cons(x, Nil()))) == app(rev(Cons(x, Nil())), rev(rev(xs)))
                          // l == app(rev(Cons(x, Nil())), rev(rev(xs)))
    }
  } ensuring {res => res && rev(rev(l)) == l}

  def rev_rev_lemma1(l: List):Boolean = {
    l match {
      case Nil() => true
      case Cons(x, xs) =>  rev_rev_lemma(xs)
                          // rev(rev(l)) == l
                          // rev(app(rev(xs), Cons(x, Nil()))) == app(rev(Cons(x, Nil())), rev(rev(xs)))
                          // l == app(rev(Cons(x, Nil())), rev(rev(xs)))
    }
  } ensuring {res => res && rev(rev(l)) == l}

  @induct
  def rev_rev_lemma4(l: List): Boolean = { rev(rev(l)) == l } holds

  def rev_rev_lemma2(l: List):Boolean = {
    l match {
      case Nil() => rev(rev(l)) == l
      case Cons(x, xs) => rev_rev_lemma(xs) && rev(rev(Cons(x,xs))) == Cons(x, xs) &&
                          // rev(app(rev(xs), Cons(x, Nil()))) == app(rev(Cons(x, Nil())), rev(rev(xs)))
                          app(Cons(x, Nil()), rev(rev(xs))) != Nil()
    }
  } holds

  def rev_rev_lemma3(xs: List, x: Int): Boolean =  { 
    rev(rev(Cons(x, xs))) == Cons(x, xs)
  } holds
}

