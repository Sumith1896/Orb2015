package lazydatastructures

import leon.stats._
import leon.collection._
import leon.annotation._
import withOrb._
import scala.util.Random
import scala.math.BigInt

object TestEngine {
  /**
   * A test that compares the performance of eager and lazy concatenation
   */
  def concatTest() {
    println("Running concat test...")
    import Concat._
    val length = 1000000
    val k = 10
    val iterCount = 10
    val l1 = (0 until length).foldRight(List[BigInt]()){
      case (i, acc) => i :: acc
    }
    val l2 = (0 until length).foldRight(List[BigInt]()){
      case (i, acc) => 2*i :: acc
    }
    println("Created inputs, starting operations...")
    def iterate[T](op: => BigInt) = {
      var res = BigInt(0)
      var i = iterCount
      while (i > 0) {
        res = op
        i -= 1
      }
      res
    }
    val elem1 = timed{ iterate((l1 ++ l2)(k)) } {t => println(s"Eager Concat completed in ${t/1000.0} sec") }
    println(s"$k th element of concatenated list: $elem1")
    val elem2 = timed{ iterate(concatnSelect(l1, l2, k).get) }{t => println(s"Lazy ConcatnSelect completed in ${t/1000.0} sec") }
    println(s"$k th element of concatenated list: $elem2")
    assert(elem1 == elem2)
  }
  
  def buMsortTest() {
    println("Running merge sort test...")
    import BottomUpMergeSort._
    import listalgorithms.MergeSort
    val length = 1000000
    val randomList = Random.shuffle((0 until length).toList)
    val l1 = randomList.foldRight(List[BigInt]()){
      case (i, acc) => i :: acc
    }
    val l2 = randomList.foldRight(INil(): IList){
      case (i, acc) => ICons(BigInt(i), acc)
    } 
    println("Created inputs, starting operations...")
    val elem2 = timed{ IListToLList(l2) }{t => println(s"Lazy merge sort completed in ${t/1000.0} sec") }
    val elem1 = timed{ MergeSort.msort((x: BigInt, y: BigInt) => x <= y)(l1) } {t => println(s"Eager merge sort completed in ${t/1000.0} sec") }
    //println(s"$k th element of concatenated list: $elem1")    
    //println(s"$k th element of concatenated list: $elem2")
    //assert(elem1 == elem2)
  }

  def main(args: Array[String]) {
    //concatTest()
    buMsortTest()
  }
}
