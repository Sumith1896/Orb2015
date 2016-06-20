package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

/**
 * Implementation of the CYK algorithm 
 * Wiki - https://en.wikipedia.org/wiki/CYK_algorithm
 * Grammar is taken two lists for two types of rules in CNF -
 * G1 has A -> alpha, production rules
 * G2 has P -> LP RP, production rules
 */

object Grammar {

  abstract class RHS {
  	def valid(kn: BigInt, kt: BigInt): Boolean = {
  		this match {
  			case UnitRHS(x) => (0 <= x) && (x <= kt - 1)
  			case NonUnitRHS(x, y) => (0 <= x) && (x <= kn - 1) && (0 <= y) && (y <= kn - 1)
  		}
  	}
  }

  case class NonUnitRHS(x: BigInt, y: BigInt) extends RHS
  case class UnitRHS(x: BigInt) extends RHS
  
  def validP(P: List[(BigInt, RHS)], kn: BigInt, kt: BigInt): Boolean = {
  	P match {
  		case Cons((x, rhs), tail) => (0 <= x) && (x <= kn - 1) && rhs.valid(kn, kt) && validP(tail, kn, kt)
  		case Nil() => true
  	}
  }

  def validS(S: List[BigInt], kn: BigInt): Boolean = {
  	S match {
  		case Cons(x, tail) => (0 <= x) && (x <= kn - 1) && validS(tail, kn)
  		case Nil() => true
  	}
  }

  def validR(R: List[RHS], kn: BigInt, kt: BigInt): Boolean = {
  	R match {
  		case Cons(x, tail) => (x.valid(kn, kt) && validR(tail, kn, kt))
  		case Nil() => true
  	}
  }

  case class Grammar(P: List[(BigInt, RHS)], S: List[BigInt], kn: BigInt, kt: BigInt) {
  	def valid: Boolean = {
  		validP(P, kn, kt) && validS(S, kn)
  	}

  	@ignore
  	var boolArr = Array[Boolean]()
	  @extern
	  def derives(N: BigInt, w: BigInt): Boolean = {
	  	boolArr(w.toInt)
	  } ensuring(_ => time <= 1)

	  @ignore
	  var listRhs = List[RHS]()
	  @extern
	  def rhs(N: BigInt): List[RHS] = {
	  	listRhs
	  } ensuring(res => validR(res, kn, kt) && res.size <= 100 && time <= 1)
  }

  
}

object CYK {
	import Grammar._

  @ignore
  var string = Array[BigInt]()

  @extern
  def A(i: BigInt): BigInt = {
  	string(i.toInt)
  } ensuring(_ => time <= 1)

  def deps(i: BigInt, n: BigInt, g: Grammar): Boolean = {
		require(i >= 0 && n >= i && g.kn > 0)
		if(i <= 0) true
		else columnsCachedfrom(i - 1, n, g)
	}

	def columnsCachedfrom(i: BigInt, n: BigInt, g: Grammar): Boolean = {
		require(i >= 0 && n > i && g.kn > 0)
		columnCached(n - 1, i, n, g) && {
		if(i <= 0) true
		else columnsCachedfrom(i - 1, n, g)
		} 
	}

	def columnCached(j: BigInt, i: BigInt, n: BigInt, g: Grammar): Boolean = {
		require(i >= 0 && j >= 0 && n > i && n > j && g.kn > 0)
		cellCached(g.kn - 1, j, i, n, g) && {
		if(j <= 0) true
		else columnCached(j - 1, i, n, g)
		}
  }

  def cellCached(N: BigInt, j: BigInt, i: BigInt, n: BigInt, g: Grammar): Boolean = {
  	require(N >= 0 && g.kn > N && i >= 0 && j >= 0 && n > i && n > j)
  	cyk(N, j, i, n, g).cached 	&& {
		if(N <= 0) true
		else cellCached(N - 1, j, i, n, g)
		}
  }

  @axiom
  def cachedLem(N: BigInt, J: BigInt, I: BigInt, i: BigInt, n: BigInt, g: Grammar): Boolean = {
  	require(N >= 0 && J >= 0 && I >= 0 && n > J && n > I && i >= I)
  	columnsCachedfrom(i - 1, n, g) ==> cyk(N, J, I, n, g).cached && deps(I, n, g)
  }

  @invstate
  def checkPartitionSat(k: BigInt, l: BigInt, r: BigInt, j: BigInt, i: BigInt, n: BigInt, g: Grammar): Boolean = {
  	require(k >= 0 && i >= k && l >= 0 && r >= 0 && j >= 0 && i > 0 && n > j + i && g.kn > 0 && deps(i, n, g) && cachedLem(l, j, k, i, n, g) && cachedLem(r, j + k, i - k, i, n, g))
  	if(k == i) false
  	else {
  		val check = cyk(l, j, k, n, g) && cyk(r, j + k, i - k, n, g)
  		if(check) true
  		else checkPartitionSat(k + 1, l, r, j, i, n, g)
  	}
  } ensuring(_ => time <= ? * (i - k) + ?)

  @invstate
	def goThroughList(P: List[RHS], j: BigInt, i: BigInt, n:BigInt, g: Grammar): Boolean = {
		require(validR(P, n, n) && i > 0 && j >= 0 && n > j + i && g.kn > 0 && P.size <= 100 && deps(i, n, g))
		P match {
			case Nil() => false
			case Cons(x, tail) => {
				x match {
					case UnitRHS(_) => false
					case NonUnitRHS(l, r) => 
						checkPartitionSat(BigInt(0), l, r, j, i, n, g) || goThroughList(tail, j, i, n, g)
				}
			}
		}
	} ensuring(_ => (P.size <= 100 ==> time <= ? * i + ?))

	@invstate
  @memoize
  def cyk(N: BigInt, j: BigInt, i: BigInt, n:BigInt, g: Grammar): Boolean = {
  	require(validR(g.rhs(N), n, n) && N >= 0 && j >= 0 && i >= 0 && n > j + i && g.kn > 0 && deps(i, n, g))
  	if(i == 0) {
  		g.derives(N, A(j))
  	} else {
  		val l = g.rhs(N) // l is a list of RHS
  		goThroughList(l, j, i, n, g)
  	}
  } ensuring(_ => time <= ? * i + ?)

  // def fill3D(k: BigInt, j: BigInt, i: BigInt, n:BigInt, g: Grammar): BigInt = {
  // 	if(k == g.kn) BigInt(0)
  // 	else {
		// 	val x = cyk(k, j, i, n, g)
		// 	fill3D(k + 1, j, i, n, g)
		// }  
  // } ensuring(_ => time <= ? * ((g.kn - k) * i) + ?)

  // def fillColumns(j: BigInt, i: BigInt, n:BigInt, g: Grammar): BigInt = {
  // 	if(j == n - i) BigInt(0)
  // 	else {
  // 		val x = fill3D(BigInt(0), j, i, n, g)
  // 		fillColumns(j + 1, i, n, g)
  // 	}
  // } ensuring(_ => time <= ? * ((n - j) * (g.kn)) + ?)

  // def fillRows(i: BigInt, n: BigInt, g: Grammar): BigInt = {
  // 	if(i == n) BigInt(0)
  // 	else {
  // 		val x = fillColumns(0, i, n, g)
  // 		fillRows(i + 1, n, g)
  // 	}
  // } ensuring(_ => time <= ? * ((i - n) * n * (g.kn)) + ?)

  // def fillTable(n: BigInt, g: Grammar): BigInt = {
  // 	fillRows(0, n, g)
  // }

  // def checkStart(i: BigInt, n: BigInt, g: BigInt, s: BigInt): Boolean = {
  // 	if(i == g) false
  // 	else {
  // 		if(cyk(n, 0, i)) true
  // 		else checkStart(i + 1, n, g, s)
  // 	}
  // }

  // def cykSols(n: BigInt, g: Grammar): Boolean = {
  // 	fillTable(n, g)
  // 	checkStart(0, n, g)
  // }


}
