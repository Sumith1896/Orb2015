import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object SortedList {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= BigInt(0))

  //def sizeSynth(l: List): BigInt = choose{ (i: BigInt) => i >= 0 && sizeSynth(Cons(0, l)) == i + 1}

  def content(l: List): Set[BigInt] = l match {
    case Nil() => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def groundSynth() = choose{ (out: List) => size(out) == 5 }

  def insertSynth(in: List, v: BigInt) = choose{ (out: List) => content(out) == content(in) ++ Set(v) }

  def tailSynth(in: List) = choose{out: List => size(out)+1 == size(in)}
  def consSynth(in: List) = choose{out: List => size(out) == size(in)+1}

  def listOfSizeSynth(i: BigInt) = {
    require(i >= 0)
    choose { out: List => size(out) == i }
  }

  def insert1(l: List, v: BigInt) = (
    Cons(v, l)
  ) ensuring(res => content(res) == content(l) ++ Set(v) && size(res) >= size(l))

  def insert2(l: List, v: BigInt): List = (l match {
    case Nil() => Cons(v, Nil())
    case Cons(x, tail) => if (x == v) l else Cons(x, insert2(tail, v))
  }) ensuring(res => content(res) == content(l) ++ Set(v) && size(res) >= size(l))

  def insert3(l: List, v: BigInt): List = {
    require(isStrictlySorted(l))

    l match {
      case Nil() => Cons(v, Nil())
      case Cons(x, tail) =>
        if (v < x) {
          Cons(v, l)
        } else if (v == x) {
          l
        } else {
          Cons(x, insert3(tail, v))
        }
    }
  } ensuring(res => content(res) == content(l) ++ Set(v) && size(res) >= size(l))

  def deleteSynth(in: List, v: BigInt) = choose{ (out: List) => !(content(out) contains v) }

  def delete1(l: List, v: BigInt): List = (l match {
      case Nil() => Nil()
      case Cons(x, tail) => if (x == v) delete1(tail, v) else Cons(x, delete1(tail, v))
    }) ensuring(res => !(content(res) contains v) && size(res) <= size(l))

  //def delete2(l: List, v: BigInt): List = {
  //  require(isStrictlySorted(l))

  //  l match {
  //    case Nil() => Nil()
  //    case Cons(x, tail) =>
  //      if (x == v) {
  //        tail
  //      } else {
  //        Cons(x, delete2(tail, v))
  //      }
  //  }
  //} ensuring(res => !(content(res) contains v) && size(res) <= size(l))

  def contains(list : List, elem : BigInt) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => if(elem == x) true else contains(xs, elem)
  }) ensuring(res => res == content(list).contains(elem))

  def deleteMagic(head: BigInt, tail: List, toDelete: BigInt): List = ({
    //require(isStrictlySorted(Cons(head, tail)) && toDelete < head);
    require(isStrictlySorted(Cons(toDelete, Cons(head, tail))))

    Cons(head, tail)
  })ensuring(res => !(content(res) contains toDelete))

  def delete3(l: List, v: BigInt): List = {
    require(isStrictlySorted(l))

    l match {
      case Nil() => Nil()
      case Cons(x, tail) =>
        if (x == v) {
          tail
        } else if (v < x) {
          deleteMagic(x, tail, v)
        } else {
          Cons(x, delete3(tail, v))
        }
    }
  } ensuring(res => !(content(res) contains v) && size(res) <= size(l))

  @induct
  def isStrictlySorted(l: List): Boolean = (l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, xs @ Cons(y, ys)) => {
      if(x < y) {
        if(isStrictlySorted(xs)) discard(ltaLemma(x, y, ys)) else false
      } else {
        false
      }
    }
  }) ensuring(res => !res || (l match {
    case Nil() => true
    case Cons(x, xs) => lessThanAll(x, xs)
  }))

  def lessThanAll(x : BigInt, l : List) : Boolean = (l match {
    case Nil() => true
    case Cons(y, ys) => if(x < y) lessThanAll(x, ys) else false
  }) ensuring(res => !res || !contains(l, x))

  def discard(value : Boolean) = true
  
  @induct
  def ltaLemma(x : BigInt, y : BigInt, l : List) : Boolean = {
    require(lessThanAll(y, l) && x < y)
    lessThanAll(x, Cons(y, l))
  } holds 

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }
}
