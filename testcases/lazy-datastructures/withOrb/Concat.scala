package withOrb

import leon._
import lazyeval._
import lazyeval.Lazy._
import lang._
import annotation._
import instrumentation._
import collection._
import invariant._

object Concat {
  sealed abstract class LList[T] {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: Lazy[LList[T]]) extends LList[T]
  case class SNil[T]() extends LList[T]
  def ssize[T](l: Lazy[LList[T]]): BigInt = (l*).size

  def concat[T](l1: List[T], l2: List[T]): LList[T] = {
    l1 match {
      case Cons(x, xs) => SCons(x, $(concat(xs, l2)))
      case Nil()       => SNil[T]()
    }
  } ensuring { _ => time <= ? }

  def kthElem[T](l: Lazy[LList[T]], k: BigInt): Option[T] = {
    require(k >= 0)
    l.value match {
      case SCons(x, xs) =>
        if (k == 0) Some(x)
        else
          kthElem(xs, k - 1)
      case SNil() => None[T]
    }
  } ensuring (_ => time <= ? * k + ?)

  def concatnSelect[T](l1: List[T], l2: List[T], k: BigInt): Option[T] = {
    require(k >= 0)
    kthElem($(concat(l1, l2)), k)
  } ensuring (_ => time <= ? * k + ?)
}
