scalac -optimise -d testbin $(find ./library/ -name "*.scala" | xargs) testcases/orb-runtime/package.scala ./testcases/lazy-datastructures/withOrb/Concat.scala  ./testcases/lazy-datastructures/withOrb/BottomUpMegeSort.scala ./testcases/verification/list-algorithms/BasicMergeSort.scala ./testcases/lazy-datastructures/withOrb/RealTimeQueue.scala ./testcases/orb-testcases/timing/AmortizedQueue.scala
