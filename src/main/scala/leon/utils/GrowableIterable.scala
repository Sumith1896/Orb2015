/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable.ArrayBuffer

class GrowableIterable[T](init: Seq[T], growth: Iterator[T]) extends Iterable[T] {
  private var buffer = new ArrayBuffer[T]() ++ init

  var canGrow = () => true

  private val cachingIterator = new Iterator[T] {
    def hasNext = canGrow() && growth.hasNext

    def next() = {
      val res = growth.next()
      buffer += res
      res
    }
  }

  def += (more: T)      = buffer +=  more
  def ++=(more: Seq[T]) = buffer ++= more
  def -= (less: T)      = buffer -=  less
  def --=(less: Seq[T]) = buffer --= less

  def iterator: Iterator[T] = {
    buffer.iterator ++ cachingIterator
  }

  def sortBufferBy[B](f: T => B)(implicit ord: math.Ordering[B]) = {
    buffer = buffer.sortBy(f)
  }
}
