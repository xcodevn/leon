/* Expression compiler correctness.
   Filip Maric and Viktor Kuncak
*/
import leon.Utils._
import leon.Annotations._

object BT {
  sealed abstract class Sign
  case class NUM(x : Int) extends Sign
  case class PLUS extends Sign

  sealed abstract class List0
  case class Cons0(head : Sign, tail : List0) extends List0
  case class Nil0() extends List0
  def single(x: Sign) = Cons0(x, Nil0())
  
  sealed abstract class Expr
  case class Num(x: Int) extends Expr
  case class Plus(e1: Expr, e2: Expr) extends Expr
 
  def eval(e: Expr) : Int = {
   e match {
     case Num(x) => x
     case Plus(e1, e2) => eval(e1) + eval(e2)
   }
 }
 
 def postfixAcc(e : Expr, acc : List0) : List0 = {
   e match {
     case Num(x) => Cons0(NUM(x),acc)
     case Plus(e1, e2) => postfixAcc(e1, postfixAcc(e2, Cons0(PLUS(), acc)))
   }
 }
 
 sealed abstract class Stack
 case class Empty extends Stack
 case class Push(i: Int, s: Stack) extends Stack
 
 def run(l:List0, s: Stack) : Stack = {
   l match {
     case Nil0() => s
     case Cons0(NUM(x), ss) => run(ss, Push(x, s))
     case Cons0(PLUS(), ss) => s match {
       case Push(a, Push(b, s1)) => run(ss, (Push(a + b, s1)))
       case _ => Empty()
     }
   }
 }

 @induct
 def run_lemma(e: Expr, post: List0, stack: Stack) = {
   run(postfixAcc(e, post), stack) == run(post, Push(eval(e), stack))
 } holds

  // we express induction with generalization using appropriate recursion
 def run_lemma_induct(e: Expr, ss: List0, stack: Stack) : Boolean = {
   e match {
     case Num(x) => run_lemma(e, ss, stack)
     case Plus(e1, e2) => run_lemma(e, ss, stack) && 
       run_lemma_induct(e1, postfixAcc(e2, Cons0(PLUS(), ss)), stack) &&
       run_lemma_induct(e2, Cons0(PLUS(),ss), Push(eval(e1), stack))
   }
 } holds

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

  @lemma @induct @simp
  def appnil_lemma(l: List) = { app(l, Nil() ) == l } holds

  @lemma @induct @simp
  def app_assoc_lemma(l1: List, l2: List, l3: List) = { app(l1, app(l2, l3)) == app( app(l1, l2), l3) } holds

  @lemma @induct @simp
  def rev_app_lemma(l1: List, l2: List) = {
    rev(app(l1, l2)) == app(rev(l2), rev(l1))
  } holds


  @induct
  def rev_rev_lemma(l: List):Boolean = {
    rev(rev(l)) == l
  } holds

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
    7 == nat2Int(plus(int2Nat(3), int2Nat(4)))
    //Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero()))))))) == plus( Succ(Succ(Succ(Zero()))), Succ(Succ(Succ(Succ(Zero())))))
  } holds


  @induct @depend() @simp
  def plus_zero_lemma(a: Nat): Boolean = {
    plus(a, Zero()) == a
  } holds

  @simp @induct @depend()
  def sub_zero_lemma(a: Nat): Boolean = {
    sub(a, Zero()) == a
  } holds

  @simp @induct @depend()
  def assoc_plus_lemma(a: Nat, b: Nat, c: Nat): Boolean = {
    plus(a, plus(b, c)) == plus(plus(a, b), c)
  } holds
  
  @depend()
  def zero_sub_lemma(a: Nat): Boolean = {
    sub(Zero(), a) == a
  } holds

  def one() = Succ(Zero())

  @simp @induct @depend()
  def plusOne_lemma1(a: Nat): Boolean = {
    plus(one(), a) == Succ(a)
  } holds

  @simp @induct @depend()
  def plusOne_lemma2(a: Nat): Boolean = {
    plus(a, one()) == Succ(a)
  } holds

  @lemma @depend()
  def plus_lemma(a: Nat, b: Nat, c: Nat): Boolean = {
    require (a == b)
    plus(a, c) == plus(b, c)
  } holds

  @simp @induct
  def spll(a: Nat, b: Nat): Boolean = {
    Succ(plus(a, b)) == plus(a, Succ(b))
  } holds
  
  @induct
  def swap_plus_lemma(a: Nat, b: Nat): Boolean =  {
    plus(a, b) == plus(b, a) 
  } holds

  def isOdd(n: Nat): Boolean = n match {
    case Zero()      => false
    case Succ(n1)   => ! isOdd(n1)
  }

  def isEven(n: Nat) = !isOdd(n)

  def three_odd_lemma2() = {isOdd(int2Nat(9)) } holds

  @lemma
  def sumEven_lemma1(n1: Nat, n2: Nat): Boolean = {
    require(isEven(n1) && isEven(n2))
    n1 match {
      case Zero() => true
      case Succ(Succ(n10)) => sumEven_lemma(n10, n2)
    }
  } ensuring {res => res && isEven(plus(n1,n2))}
  
  @lemma
  def sumEven_lemma(n1: Nat, n2: Nat): Boolean  ={
    require(isEven(n1) && isEven(n2))
    sumEven_lemma1(n1,n2) && isEven(plus(n1,n2))
  } holds
    
  @lemma @induct @simp
  def succSuccPlus_lemma(n1: Nat, n2: Nat): Boolean = {
    plus(Succ(n1), Succ(n2)) == Succ(Succ(plus(n1, n2)))
  } holds
  
  @lemma @simp
  def negative_lemma(n: Nat): Boolean = {
    !isOdd(n) == isEven(n)
  } holds
  
  /*
  @lemma @simp
  def sol2(a: Nat, b: Nat): Boolean = {
    isEven(plus(a, Succ(Succ(b)))) == isEven(plus(a, b))
  } holds
  
  @lemma @depend("sumEven_lemma", "negative_lemma")
  def sol1(n1: Nat, n2: Nat): Boolean = {
    require(isEven(n1) && isEven(n2))
    isEven(plus(Succ(n1), Succ(n2)))
  } holds
  
  
  @depend("negative_lemma", "sol1")
  def sumOdd_lemma(n1: Nat, n2: Nat): Boolean = {
    require(isOdd(n1) && isOdd(n2))
    (n1, n2) match {
      case (Succ(n10), Succ(n20)) => isEven(n10) && isEven(n20) && sumEven_lemma(n10, n20)
    }
  } ensuring {res => res && isEven(plus(n1, n2))}

  */
  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }
  
  def asList(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && content(res) == content(l1) ++ content(l2))

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def isEmpty(queue : AbsQueue) : Boolean = queue match {
    case Queue(Nil(), Nil()) => true
    case _ => false
  }

  def reverse(l : List) : List = (l match {
    case Nil() => Nil()
    case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil()))
  }) ensuring (content(_) == content(l))

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  } ensuring(isAmortized(_))

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(isAmortized(_))

  def tail(queue : AbsQueue) : AbsQueue = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
    }
  } ensuring (isAmortized(_))

  def front(queue : AbsQueue) : Int = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, _), _) => f
    }
  }

  // @induct
  // def propEnqueue(rear : List, front : List, list : List, elem : Int) : Boolean = {
  //   require(isAmortized(Queue(front, rear)))
  //   val queue = Queue(front, rear)
  //   if (asList(queue) == list) {
  //     asList(enqueue(queue, elem)) == concat(list, Cons(elem, Nil()))
  //   } else
  //     true
  // }.holds

  @induct
  def propFront(queue : AbsQueue, list : List, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    if (asList(queue) == list) {
      list match {
        case Cons(x, _) => front(queue) == x
      }
    } else
      true
  }.holds

  @induct
  def propTail(rear : List, front : List, list : List, elem : Int) : Boolean = {
    require(!isEmpty(Queue(front, rear)) && isAmortized(Queue(front, rear)))
    if (asList(Queue(front, rear)) == list) {
      list match {
        case Cons(_, xs) => asList(tail(Queue(front, rear))) == xs
      }
    } else
      true
  } //.holds

  def enqueueAndFront(queue : AbsQueue, elem : Int) : Boolean = {
    if (isEmpty(queue))
      front(enqueue(queue, elem)) == elem
    else
      true
  }.holds

  def enqueueDequeueThrice(queue : AbsQueue, e1 : Int, e2 : Int, e3 : Int) : Boolean = {
    if (isEmpty(queue)) {
      val q1 = enqueue(queue, e1)
      val q2 = enqueue(q1, e2)
      val q3 = enqueue(q2, e3)
      val e1prime = front(q3)
      val q4 = tail(q3)
      val e2prime = front(q4)
      val q5 = tail(q4)
      val e3prime = front(q5)
      e1 == e1prime && e2 == e2prime && e3 == e3prime
    } else
      true
  }.holds

  sealed abstract class KeyValuePairAbs
  case class KeyValuePair(key: Int, value: Int) extends KeyValuePairAbs

  sealed abstract class AList
  case class ACons(head: KeyValuePairAbs, tail: AList) extends AList
  case class ANil() extends AList

  sealed abstract class OptionInt
  case class Some(i: Int) extends OptionInt
  case class None() extends OptionInt

  def domain(l: AList): Set[Int] = l match {
    case ANil() => Set.empty[Int]
    case ACons(KeyValuePair(k,_), xs) => Set(k) ++ domain(xs)
  }

  def find(l: AList, e: Int): OptionInt = l match {
    case ANil() => None()
    case ACons(KeyValuePair(k, v), xs) => if (k == e) Some(v) else find(xs, e)
  }

  def noDuplicates(l: AList): Boolean = l match {
    case ANil() => true
    case ACons(KeyValuePair(k, v), xs) => find(xs, k) == None() && noDuplicates(xs)
  }

  def updateAll(l1: AList, l2: AList): AList = (l2 match {
    case ANil() => l1
    case ACons(x, xs) => updateAll(updateElem(l1, x), xs)
  }) ensuring(domain(_) == domain(l1) ++ domain(l2))

  def updateElem(l: AList, e: KeyValuePairAbs): AList = (l match {
    case ANil() => ACons(e, ANil())
    case ACons(KeyValuePair(k, v), xs) => e match {
      case KeyValuePair(ek, ev) => if (ek == k) ACons(KeyValuePair(ek, ev), xs) else ACons(KeyValuePair(k, v), updateElem(xs, e))
    }
  }) ensuring(res => e match {
    case KeyValuePair(k, v) => domain(res) == domain(l) ++ Set[Int](k)
  })

  @induct
  def readOverWrite(l: AList, k1: Int, k2: Int, e: Int) : Boolean = {
    find(updateElem(l, KeyValuePair(k2,e)), k1) == (if (k1 == k2) Some(e) else find(l, k1))
  }.holds

  abstract sealed class A
  case class B(size: Int) extends A
  case object C extends A

  def foo(): A = {
    C
  }

  def foo1(a: A): A = a match {
    case C => a
    case B(s) => a 
  }

  def foo2(a: A): A = a match {
    case c @ C => c
    case B(s) => a
  }

  def listOfSize(i: Int): List = {
    require(i >= 0)

    if (i == 0) {
      Nil()
    } else {
      choose { (res: List) => size(res) == i }
    }
  } ensuring ( size(_) == i )


  def listOfSize2(i: Int): List = {
    require(i >= 0)

    if (i > 0) {
      Cons(0, listOfSize(i-1))
    } else {
      Nil()
    }
  } ensuring ( size(_) == i )

  abstract sealed class A1
  case class B1(size: Int) extends A1

  def foo1(): Int = {
    val b = B1(3)
    b.size
  } ensuring(_ == 3)

  // These finite sorting functions essentially implement insertion sort.
  def sort2(x : Int, y : Int) : (Int,Int) = {
    if(x < y) (x, y) else (y, x)
  } ensuring (_ match {
    case (a, b) => a <= b && Set(a,b) == Set(x,y)
  })

  def sort3(x1 : Int, x2 : Int, x3 : Int) : (Int, Int, Int) = {
    val (x1s, x2s) = sort2(x1, x2)

    if(x2s <= x3) {
      (x1s, x2s, x3)
    } else if(x1s <= x3) {
      (x1s, x3, x2s)
    } else {
      (x3, x1s, x2s)
    }
  } ensuring (_ match {
    case (a, b, c) => a <= b && b <= c && Set(a,b,c) == Set(x1,x2,x3)
  })

  def sort4(x1 : Int, x2 : Int, x3 : Int, x4 : Int) : (Int, Int, Int, Int) = {
    val (x1s, x2s, x3s) = sort3(x1, x2, x3)

    if(x3s <= x4) {
      (x1s, x2s, x3s, x4)
    } else if(x2s <= x4) {
      (x1s, x2s, x4, x3s)
    } else if(x1s <= x4) {
      (x1s, x4, x2s, x3s)
    } else {
      (x4, x1s, x2s, x3s)
    }
  } ensuring (_ match {
    case (a, b, c, d) => a <= b && b <= c && c <= d && Set(a,b,c,d) == Set(x1,x2,x3,x4)
  })

  def sort5(x1 : Int, x2 : Int, x3 : Int, x4 : Int, x5 : Int) : (Int, Int, Int, Int, Int) = {
    val (x1s, x2s, x3s, x4s) = sort4(x1, x2, x3, x4)

    if(x4s <= x5) {
      (x1s, x2s, x3s, x4s, x5)
    } else if(x3s <= x5) {
      (x1s, x2s, x3s, x5, x4s)
    } else if(x2s <= x5) {
      (x1s, x2s, x5, x3s, x4s)
    } else if(x1s <= x5) {
      (x1s, x5, x2s, x3s, x4s)
    } else {
      (x5, x1s, x2s, x3s, x4s)
    }
  } ensuring (_ match {
    case (a, b, c, d, e) => a <= b && b <= c && c <= d && d <= e && Set(a,b,c,d,e) == Set(x1,x2,x3,x4,x5)
  })

  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Data type definitions */
  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  private case class Node(rank : Int, elem : Int, nodes : Heap)
  
  sealed abstract class Heap
  private case class  Nodes(head : Node, tail : Heap) extends Heap
  private case object EmptyH extends Heap
  
  sealed abstract class OptInt
  case class SomeH(value : Int) extends OptInt
  case object NoneH extends OptInt
  
  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Abstraction functions */
  /*~~~~~~~~~~~~~~~~~~~~~~~*/
  def heapContent(h : Heap) : Set[Int] = h match {
    case EmptyH => Set.empty[Int]
    case Nodes(n, ns) => nodeContent(n) ++ heapContent(ns)
  }
  
  def nodeContent(n : Node) : Set[Int] = n match {
    case Node(_, e, h) => Set(e) ++ heapContent(h)
  }
  
  /*~~~~~~~~~~~~~~~~~~~~~~~~*/
  /* Helper/local functions */
  /*~~~~~~~~~~~~~~~~~~~~~~~~*/
  private def reverse(h : Heap) : Heap = reverse0(h, EmptyH)
  private def reverse0(h : Heap, acc : Heap) : Heap = (h match {
    case EmptyH => acc
    case Nodes(n, ns) => reverse0(ns, Nodes(n, acc))
  }) ensuring(res => heapContent(res) == heapContent(h) ++ heapContent(acc))
  
  private def link(t1 : Node, t2 : Node) = (t1, t2) match {
    case (Node(r, e1, ns1), Node(_, e2, ns2)) =>
      if(e1 <= e2) {
        Node(r + 1, e1, Nodes(t2, ns1))
      } else {
        Node(r + 1, e2, Nodes(t1, ns2))
      }
  }
  
  private def insertNode(t : Node, h : Heap) : Heap = (h match {
    case EmptyH => Nodes(t, EmptyH)
    case Nodes(t2, h2) =>
      if(t.rank < t2.rank) {
        Nodes(t, h)
      } else {
        insertNode(link(t, t2), h2)
      }
  }) ensuring(res => heapContent(res) == nodeContent(t) ++ heapContent(h))
  
  private def getMin(h : Heap) : (Node, Heap) = {
    require(h != EmptyH)
    h match {
      case Nodes(t, EmptyH) => (t, EmptyH)
      case Nodes(t, ts) =>
        val (t0, ts0) = getMin(ts)
        if(t.elem < t0.elem) {
          (t, ts)
        } else {
          (t0, Nodes(t, ts0))
        }
    }
  } ensuring(_ match {
    case (n,h2) => nodeContent(n) ++ heapContent(h2) == heapContent(h)
  })
  
  /*~~~~~~~~~~~~~~~~*/
  /* Heap interface */
  /*~~~~~~~~~~~~~~~~*/
  def empty() : Heap = {
    EmptyH
  } ensuring(res => heapContent(res) == Set.empty[Int])
  
  def isEmpty(h : Heap) : Boolean = {
    (h == EmptyH)
  } ensuring(res => res == (heapContent(h) == Set.empty[Int]))
  
  def insert(e : Int, h : Heap) : Heap = {
    insertNode(Node(0, e, EmptyH), h)
  } ensuring(res => heapContent(res) == heapContent(h) ++ Set(e))
  
  def merge(h1 : Heap, h2 : Heap) : Heap = ((h1,h2) match {
    case (_, EmptyH) => h1
    case (EmptyH, _) => h2
    case (Nodes(t1, ts1), Nodes(t2, ts2)) =>
      if(t1.rank < t2.rank) {
        Nodes(t1, merge(ts1, h2))
      } else if(t2.rank < t1.rank) {
        Nodes(t2, merge(h1, ts2))
      } else {
        insertNode(link(t1, t2), merge(ts1, ts2))
      }
  }) ensuring(res => heapContent(res) == heapContent(h1) ++ heapContent(h2))
  
  def findMin(h : Heap) : OptInt = (h match {
    case EmptyH => NoneH
    case Nodes(Node(_, e, _), ns) =>
      findMin(ns) match {
        case NoneH => SomeH(e)
        case SomeH(e2) => SomeH(if(e < e2) e else e2)
      }
  }) ensuring(_ match {
    case NoneH => isEmpty(h)
    case SomeH(v) => heapContent(h).contains(v)
  })

  def deleteMin(h : Heap) : Heap = (h match {
    case EmptyH => EmptyH
    case ts : Nodes =>
      val (Node(_, e, ns1), ns2) = getMin(ts)
      merge(reverse(ns1), ns2)
  }) ensuring(res => heapContent(res).subsetOf(heapContent(h)))
  
  def sanity0() : Boolean = {
    val h0 : Heap = EmptyH
    val h1 = insert(42, h0)
    val h2 = insert(72, h1)
    val h3 = insert(0, h2)
    findMin(h0) == NoneH &&
    findMin(h1) == SomeH(42) &&
    findMin(h2) == SomeH(42) &&
    findMin(h3) == SomeH(0)
  }.holds
  
  def sanity1() : Boolean = {
    val h0 = insert(42, EmptyH)
    val h1 = insert(0, EmptyH)
    val h2 = merge(h0, h1)
    findMin(h2) == SomeH(0)
  }.holds
  
/*
  def sanity3() : Boolean = {
    val h0 = insert(42, insert(0, insert(3, insert(12, EmptyH))))
    val h1 = deleteMin(h0)
    findMin(h1) == SomeH(3)
  }.holds

  def min(l : List) : OptInt = l match {
    case Nil() => NoneH
    case Cons(x, xs) => min(xs) match {
      case NoneH => SomeH(x)
      case SomeH(x2) => if(x < x2) SomeH(x) else SomeH(x2)
    }
  }
*/

  def isSorted1(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted1(Cons(y, ys))
  }   

  def sortedIns(e: Int, l: List): List = {
    require(isSorted1(l))
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    } 
  } ensuring(res => content(res) == content(l) ++ Set(e) 
                    && isSorted1(res)
                    && size(res) == size(l) + 1
            )

  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))
  }) ensuring(res => content(res) == content(l) 
                     && isSorted1(res)
                     && size(res) == size(l)
             )

  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(sort(ls))
  }

  abstract class A2
  case class B2(i: Int) extends A2
  case class C2(i: Int) extends A2

  def foo2(): Int = {
    require(C2(3).isInstanceOf[C2])
    val b: A2 = B2(2)
    if(b.isInstanceOf[B2])
      0
    else
      -1
  } ensuring(_ == 0)

  def bar2(): Int = foo2()

  sealed abstract class IntPairList
  case class IPCons(head: IntPair, tail: IntPairList) extends IntPairList
  case class IPNil() extends IntPairList

  sealed abstract class IntPair
  case class IP(fst: Int, snd: Int) extends IntPair

  def size1(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size1(t)
  }) ensuring(res => res >= 0)

  def iplSize(l: IntPairList) : Int = (l match {
    case IPNil() => 0
    case IPCons(_, xs) => 1 + iplSize(xs)
  }) ensuring(_ >= 0)

  def zip(l1: List, l2: List) : IntPairList = {
    // try to comment this and see how pattern-matching becomes
    // non-exhaustive and post-condition fails
    require(size(l1) == size(l2))

    l1 match {
      case Nil() => IPNil()
      case Cons(x, xs) => l2 match {
        case Cons(y, ys) => IPCons(IP(x, y), zip(xs, ys))
      }
    }
  } ensuring(iplSize(_) == size(l1))

  def sizeTailRec(l: List) : Int = sizeTailRecAcc(l, 0)
  def sizeTailRecAcc(l: List, acc: Int) : Int = {
   require(acc >= 0)
   l match {
     case Nil() => acc
     case Cons(_, xs) => sizeTailRecAcc(xs, acc+1)
   }
  } ensuring(res => res == size(l) + acc)

  def sizesAreEquiv(l: List) : Boolean = {
    size(l) == sizeTailRec(l)
  }.holds

  def sizeAndContent(l: List) : Boolean = {
    size(l) == 0 || content(l) != Set.empty[Int]
  }.holds
  
  def drunk(l : List) : List = (l match {
    case Nil() => Nil()
    case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
  }) ensuring (size(_) == 2 * size(l))

  def reverse1(l: List) : List = reverse0(l, Nil()) ensuring(content(_) == content(l))
  def reverse0(l1: List, l2: List) : List = (l1 match {
    case Nil() => l2
    case Cons(x, xs) => reverse0(xs, Cons(x, l2))
  }) ensuring(content(_) == content(l1) ++ content(l2))

  def append(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, append(xs, l2))
  }) ensuring(content(_) == content(l1) ++ content(l2))

  @induct
  def nilAppend(l : List) : Boolean = (append(l, Nil()) == l).holds

  @induct
  def appendAssoc(xs : List, ys : List, zs : List) : Boolean =
    (append(append(xs, ys), zs) == append(xs, append(ys, zs))).holds

  @induct
  def sizeAppend(l1 : List, l2 : List) : Boolean =
    (size(append(l1, l2)) == size(l1) + size(l2)).holds

  @induct
  def concat1(l1: List, l2: List) : List = 
    concat0(l1, l2, Nil()) ensuring(content(_) == content(l1) ++ content(l2))

  @induct
  def concat0(l1: List, l2: List, l3: List) : List = (l1 match {
    case Nil() => l2 match {
      case Nil() => reverse1(l3)
      case Cons(y, ys) => {
        concat0(Nil(), ys, Cons(y, l3))
      }
    }
    case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
  }) ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))

  def test(): Map[Int, Int] = {
    Map(1 -> 2, 3 -> 4, (5, 6))
  }

  def test2(): (Int, Int) = {
    1 -> 2
  }

  def test3(): Map[Int, Int] = {
    Map()
  }

  def test4(): Map[Int, Int] = {
    Map.empty[Int, Int]
  }

  def test5(): Map[Int, Int] = {
    Map.empty[Int, Int]
  }

  sealed abstract class LList
  case class LCons(head : List, tail : LList) extends LList
  case class LNil() extends LList

  def lContent(llist : LList) : Set[Int] = llist match {
    case LNil() => Set.empty[Int]
    case LCons(x, xs) => content(x) ++ lContent(xs)
  }

  def isSorted(list : List) : Boolean = list match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def lIsSorted(llist : LList) : Boolean = llist match {
    case LNil() => true
    case LCons(x, xs) => isSorted(x) && lIsSorted(xs)
  }

  def abs(i : Int) : Int = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  def mergeSpec(list1 : List, list2 : List, res : List) : Boolean = {
    isSorted(res) && content(res) == content(list1) ++ content(list2)
  }

  def mergeFast(list1 : List, list2 : List) : List = {
    require(isSorted(list1) && isSorted(list2))

    (list1, list2) match {
      case (_, Nil()) => list1
      case (Nil(), _) => list2
      case (Cons(x, xs), Cons(y, ys)) =>
        if(x <= y) {
          Cons(x, mergeFast(xs, list2)) 
        } else {
          Cons(y, mergeFast(list1, ys))
        }
    }
  } ensuring(res => mergeSpec(list1, list2, res))

  def splitSpec(list : List, res : (List,List)) : Boolean = {
    val s1 = size(res._1)
    val s2 = size(res._2)
    abs(s1 - s2) <= 1 && s1 + s2 == size(list) &&
    content(res._1) ++ content(res._2) == content(list) 
  }

  def split(list : List) : (List,List) = (list match {
    case Nil() => (Nil(), Nil())
    case Cons(x, Nil()) => (Cons(x, Nil()), Nil())
    case Cons(x1, Cons(x2, xs)) =>
      val (s1,s2) = split(xs)
      (Cons(x1, s1), Cons(x2, s2))
  }) ensuring(res => splitSpec(list, res))

  def sortSpec(in : List, out : List) : Boolean = {
    content(out) == content(in) && isSorted(out)
  }

  // Not really quicksort, neither mergesort.
  def weirdSort(in : List) : List = (in match {
    case Nil() => Nil()
    case Cons(x, Nil()) => Cons(x, Nil())
    case _ =>
      val (s1,s2) = split(in)
      mergeFast(weirdSort(s1), weirdSort(s2))
  }) ensuring(res => sortSpec(in, res))

  def toLList(list : List) : LList = (list match {
    case Nil() => LNil()
    case Cons(x, xs) => LCons(Cons(x, Nil()), toLList(xs))
  }) ensuring(res => lContent(res) == content(list) && lIsSorted(res))

  def mergeMap(llist : LList) : LList = {
    require(lIsSorted(llist))

    llist match {
      case LNil() => LNil()
      case o @ LCons(x, LNil()) => o
      case LCons(x, LCons(y, ys)) => LCons(mergeFast(x, y), mergeMap(ys))
    }
  } ensuring(res => lContent(res) == lContent(llist) && lIsSorted(res))

  def mergeReduce(llist : LList) : List = {
    require(lIsSorted(llist))

    llist match {
      case LNil() => Nil()
      case LCons(x, LNil()) => x
      case _ => mergeReduce(mergeMap(llist))
    }
  } ensuring(res => content(res) == lContent(llist) && isSorted(res))

  def mergeSort(in : List) : List = {
    mergeReduce(toLList(in))
  } ensuring(res => sortSpec(in, res))


  def map1(): Int = {
    val m = Map(1 -> 2, 2 -> 3, 3 -> 4)
    m(2)
  } ensuring(_ == 3)

  def map2(): Boolean = {
    val m1 = Map[Int, Int]()
    val m2 = Map.empty[Int, Int]
    m1 == m2
  }.holds

  def set1(): Boolean = {
    val s = Set(1, 2, 3, 4)
    s.contains(3)
  }.holds

  def set2(): Boolean = {
    val s1 = Set[Int]()
    val s2 = Set.empty[Int]
    s1 == s2
  }.holds


  def foo2(t: (Int, Int)): (Int, Int) = {
    require(t._1 > 0 && t._2 > 1)
    t
  } ensuring(res => res._1 > 0 && res._2 > 1)

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
  }) ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
  }

  def nnf(formula: Formula): Formula = (formula match {
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Implies(lhs, rhs) => Implies(nnf(lhs), nnf(rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(Literal(_)) => formula
    case Literal(_) => formula
  }) ensuring(isNNF(_))

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
  }

  def vars(f: Formula): Set[Int] = {
    require(isNNF(f))
    f match {
      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Implies(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Not(Literal(i)) => Set[Int](i)
      case Literal(i) => Set[Int](i)
    }
  }

  def fv(f : Formula) = { vars(nnf(f)) }

  @induct
  def nnfIsStable(f: Formula) : Boolean = {
    require(isNNF(f))
    nnf(f) == f
  }.holds
  
  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  }.holds

  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class EmptyR() extends Tree
  case class NodeR(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  /* We consider leaves to be black by definition */
  def isBlack(t: Tree) : Boolean = t match {
    case EmptyR() => true
    case NodeR(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case EmptyR() => true
    case NodeR(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case NodeR(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case EmptyR() => true
    case NodeR(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case NodeR(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case EmptyR() => true
  }

  def blackHeight(t : Tree) : Int = t match {
    case EmptyR() => 1
    case NodeR(Black(), l, _, _) => blackHeight(l) + 1
    case NodeR(Red(), l, _, _) => blackHeight(l)
  }

  def content(t: Tree) : Set[Int] = t match {
    case EmptyR() => Set.empty
    case NodeR(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t: Tree) : Int = (t match {
    case EmptyR() => 0
    case NodeR(_, l, v, r) => size(l) + 1 + size(r)
  }) ensuring(_ >= 0)

  // <<insert element x into the tree t>>
/*
  def ins(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    t match {
      case EmptyR() => NodeR(Red(),EmptyR(),x,EmptyR())
      case NodeR(c,a,y,b) =>
        if      (x < y)  balance(c, ins(x, a), y, b)
        else if (x == y) NodeR(c,a,y,b)
        else             balance(c,a,y,ins(x, b))
    }
  } ensuring (res => content(res) == content(t) ++ Set(x) 
                   && size(t) <= size(res) && size(res) <= size(t) + 1
                   && redDescHaveBlackChildren(res)
                   && blackBalanced(res))
*/

  def makeBlack(n: Tree): Tree = {
    require(redDescHaveBlackChildren(n) && blackBalanced(n))
    n match {
      case NodeR(Red(),l,v,r) => NodeR(Black(),l,v,r)
      case _ => n
    }
  } ensuring(res => redNodesHaveBlackChildren(res) && blackBalanced(res))

/*
  def add(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    makeBlack(ins(x, t))
  } ensuring (res => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res) && blackBalanced(res))
*/
  
  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
    NodeR(c,a,x,b) match {
      case NodeR(Black(),NodeR(Red(),NodeR(Red(),a,xV,b),yV,c),zV,d) => 
        NodeR(Red(),NodeR(Black(),a,xV,b),yV,NodeR(Black(),c,zV,d))
      case NodeR(Black(),NodeR(Red(),a,xV,NodeR(Red(),b,yV,c)),zV,d) => 
        NodeR(Red(),NodeR(Black(),a,xV,b),yV,NodeR(Black(),c,zV,d))
      case NodeR(Black(),a,xV,NodeR(Red(),NodeR(Red(),b,yV,c),zV,d)) => 
        NodeR(Red(),NodeR(Black(),a,xV,b),yV,NodeR(Black(),c,zV,d))
      case NodeR(Black(),a,xV,NodeR(Red(),b,yV,NodeR(Red(),c,zV,d))) => 
        NodeR(Red(),NodeR(Black(),a,xV,b),yV,NodeR(Black(),c,zV,d))
      case NodeR(c,a,xV,b) => NodeR(c,a,xV,b)
    }
  } ensuring (res => content(res) == content(NodeR(c,a,x,b)))// && redDescHaveBlackChildren(res))

  def contains(list : List, elem : Int) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
  })

  def firstZero(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(x, xs) => if (x == 0) 0 else firstZero(xs) + 1
  }) ensuring (res =>
    res >= 0 && (if (contains(list, 0)) {
      firstZeroAtPos(list, res)
    } else {
      res == size(list)
    }))

  def firstZeroAtPos(list : List, pos : Int) : Boolean = {
    list match {
      case Nil() => false
      case Cons(x, xs) => if (pos == 0) x == 0 else x != 0 && firstZeroAtPos(xs, pos - 1)
    }
  } 

  def goal(list : List, i : Int) : Boolean = {
    if(firstZero(list) == i) {
      if(contains(list, 0)) {
        firstZeroAtPos(list, i)
      } else {
        i == size(list)
      }
    } else {
      true
    }
  }.holds

  def max(list : List) : Int = {
    require(list != Nil())
    list match {
      case Cons(x, Nil()) => x
      case Cons(x, xs) => {
        val m2 = max(xs)
        if(m2 > x) m2 else x
      }
    }
  }

  def sum(list : List) : Int = list match {
    case Nil() => 0
    case Cons(x, xs) => x + sum(xs)
  }

  def allPos(list : List) : Boolean = list match {
    case Nil() => true
    case Cons(x, xs) => x >= 0 && allPos(xs)
  }

  def prop0(list : List) : Boolean = {
    require(list != Nil())
    !allPos(list) || max(list) >= 0
  }.holds

  @induct
  def property(list : List) : Boolean = {
    // This precondition was given in the problem but isn't actually useful :D
    // require(allPos(list))
    sum(list) <= size(list) * (if(list == Nil()) 0 else max(list))
  }.holds
}
