package withOrb

import leon._
import lazyeval._
import lazyeval.$._
import lang._
import annotation._
import collection._
import instrumentation._
import invariant._

object RealTimeQueue {

  sealed abstract class Stream[T] {
    def isEmpty: Boolean = {
      this match {
        case SNil() => true
        case _      => false
      }
    }

    def isCons: Boolean = {
      this match {
        case SCons(_, _) => true
        case _           => false
      }
    }

    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + (t*).size
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: $[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  def isConcrete[T](l: $[Stream[T]]): Boolean = {
    l.isEvaluated && (l* match {
      case SCons(_, tail) =>
        isConcrete(tail)
      case _ => true
    })
  }

  @invisibleBody
  @invstate
  def rotate[T](f: $[Stream[T]], r: List[T], a: $[Stream[T]]): Stream[T] = { // doesn't change state
    require(r.size == (f*).size + 1 && isConcrete(f))
    (f.value, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, a)
      case (SCons(x, tail), Cons(y, r1)) =>
        val newa: Stream[T] = SCons[T](y, a)
        val rot = $(rotate(tail, r1, newa)) //this creates a lazy rotate operation
        SCons[T](x, rot)
    }
  } ensuring (res => res.size == (f*).size + r.size + (a*).size && res.isCons &&
                     time <= ?)

  /**
   * Returns the first element of the stream that is not evaluated.
   */
  def firstUnevaluated[T](l: $[Stream[T]]): $[Stream[T]] = {
    if (l.isEvaluated) {
      l* match {
        case SCons(_, tail) =>
          firstUnevaluated(tail)
        case _ => l
      }
    } else
      l
  } ensuring (res => (!(res*).isEmpty || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    (res.value match {
      case SCons(_, tail) =>
        firstUnevaluated(l) == firstUnevaluated(tail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: $[Stream[T]], r: List[T], s: $[Stream[T]]) {
    def isEmpty = (f*).isEmpty
    def valid = {
      (firstUnevaluated(f) == firstUnevaluated(s)) &&
        (s*).size == (f*).size - r.size //invariant: |s| = |f| - |r|
    }
  }

  @inline
  def createQ[T](f: $[Stream[T]], r: List[T], s: $[Stream[T]]) = {
    s.value match {
      case SCons(_, tail) => Queue(f, r, tail)
      case SNil() =>
        val newa: Stream[T] = SNil()
        val rotres = $(rotate(f, r, newa))
        Queue(rotres, Nil(), rotres)
    }
  }

  def empty[T] = {
    val a: Stream[T] = SNil()
    Queue(a, Nil(), a)
  }

  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, _) => x
    }
  } //ensuring (res => res.valid && time <= ?)

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    createQ(q.f, Cons(x, q.r), q.s)
  } ensuring (res => res.valid && time <= ?)

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, nf) =>
        createQ(nf, q.r, q.s)
    }
  } ensuring (res => res.valid && time <= ?)
}
