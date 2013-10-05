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

  def length(l: List) : Int = {
    l match {
      case Nil() => 0
      case Cons(x, xs) => 1 + length(xs)
    }
  } ensuring { res => res >= 0}

  @induct @simp
  def appnil_lemma(l: List) = { app(l, Nil() ) == l } holds

  @induct @simp
  def app_assoc_lemma(l1: List, l2: List, l3: List) = { 
    app(l1, app(l2, l3)) == app( app(l1, l2), l3) 
  } holds

  @induct @simp
  def rev_app_lemma(l1: List, l2: List) = {
    rev(app(l1, l2)) == app(rev(l2), rev(l1)) 
  } holds

  @induct
  def revrev_lemma(l: List):Boolean = {
    rev(rev(l)) == l
  } holds

  def head(l: List) = {
    require(l != Nil())
    l match {
      case Cons(h, t) => h
    }
  }

  def tail(l: List) = {
    require(l != Nil())
    l match {
      case Cons(h, t) => t
    }
  }

  def s01_last(l: List): Int = {
    require(l != Nil())
    l match {
      case Cons(x, Nil()) => x
      case Cons(x, xs) => s01_last(xs)
    }
  } ensuring { res => res == head(rev(l)) }

  def s02_lastButOne(l: List): Int = {
    require(length(l) >= 2) 
    l match {
      case Cons(x1, Cons(x2, Nil())) => x1
      case Cons(x1, Cons(x2, xs)) => s02_lastButOne(Cons(x2, xs))
    }
  } ensuring { res => res == head(tail(rev(l))) }

  def s02_KthElem(k: Int, l: List): Int = {
    require(length(l) > k)
    (k, l) match {
      case (0, Cons(x, xs)) => x
      case (_, Cons(x, xs)) => s02_KthElem(k-1, xs)
    }
  } ensuring {res => res == s02_KthElem(length(l) - (k + 1) , rev(l)) }

}

