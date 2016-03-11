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
  
  /**
   * Run with Xms10G (to avoid overheads of memory allocation), and Xss1G (merge is recursive)
   */
  def buMsortTest() {
    println("Running merge sort test...")
    import BottomUpMergeSort._
    import listalgorithms.MergeSort
    val length = 3000000
    val maxIndexValue = 100
    val randomList = Random.shuffle((0 until length).toList)
    val l1 = randomList.foldRight(List[BigInt]()){
      case (i, acc) => BigInt(i) :: acc
    }
    val l2 = randomList.foldRight(INil(): IList){
      case (i, acc) => ICons(BigInt(i), acc)
    } 
    println(s"Created inputs of size (${l1.size},${l2.size}), starting operations...")
    val sort2 = timed{ mergeSort(l2) }{t => println(s"Lazy merge sort completed in ${t/1000.0} sec") }
    val sort1 = timed{ MergeSort.msort((x: BigInt, y: BigInt) => x <= y)(l1) } {t => println(s"Eager merge sort completed in ${t/1000.0} sec") }    
    // sample 10 elements from a space of [0-100]
    val rand = Random
    var totalTime1 = 0L
    var totalTime2 = 0L
    for(i <- 0 until 10) {
      val idx = rand.nextInt(maxIndexValue)
      val e1 = timed { sort1(idx) } { totalTime1 +=_ } 
      val e2 = timed { kthMin(sort2, idx) }{ totalTime2 += _ }            
      println(s"Element at index $idx - Eager: $e1 Lazy: $e1")
      assert(e1 == e2)
    }
    println(s"Time-taken to pick first 10 minimum elements - Eager: ${totalTime1/1000.0}s Lazy: ${totalTime2/1000.0}s")    
  }
  
  def rtqTest() {
    import withOrb._
    import orb._
    println("Running RTQ test...")
    val ops = 10000000
    val rand = Random
    // initialize to a queue with one element (required to satisfy preconditions of dequeue and front)
    var rtq = RealTimeQueue.empty[BigInt]
    var amq = AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil())    
    var totalTime1 = 0L
    var totalTime2 = 0L
    println(s"Testing amortized emphemeral behavior on $ops operations...")
    for(i <- 0 until ops) {
      if (!amq.isEmpty) 
        assert(RealTimeQueue.head(rtq) == amq.head)
      rand.nextInt(2) match {
        case x if x == 0 => //enqueue
//          /if(i%100000 == 0) println("Enqueue..")         
          rtq = timed{ RealTimeQueue.enqueue(BigInt(x), rtq) }{totalTime1 += _}
          amq = timed{ amq.enqueue(BigInt(x)) }{totalTime2 += _}
        case x if x == 1 => //dequeue
          if (!amq.isEmpty) {
            //if(i%100000 == 0) println("Dequeue..")         
            rtq = timed { RealTimeQueue.dequeue(rtq) } { totalTime1 += _ }
            amq = timed { amq.dequeue } { totalTime2 += _ }
          }
      }             
    }
    println(s"Ephemeral Amortized Time - Eager: ${totalTime2/1000.0}s Lazy: ${totalTime1/1000.0}s") // this should be linear in length for both cases
    // now, test worst-case behavior (in persitent mode if necessary)
    val length = (1 << 24) - 2 // a number of the form: 2^{n-2}
    // reset the queues
    rtq = RealTimeQueue.empty[BigInt]
    amq = AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil())
    // enqueue length elements
    for (i <- 0 until length) {
      rtq = RealTimeQueue.enqueue(BigInt(0), rtq)
      amq = amq.enqueue(BigInt(0))
    }
    println(s"Amortized queue size: ${amq.front.size}, ${amq.rear.size}")
    //dequeue 1 element from both queues
    timed { amq.dequeue } { t => println(s"Time to dequeue one element from Amortized Queue in the worst case: ${t/1000.0}s") }
    timed { RealTimeQueue.dequeue(rtq) } { t => println(s"Time to dequeue one element from RTQ in the worst case: ${t/1000.0}s") }    
  }

  def main(args: Array[String]) {
    //concatTest()
    //buMsortTest()
    rtqTest()
  }
}
