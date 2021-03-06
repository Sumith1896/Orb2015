/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._
import purescala.Extractors._

/** For every pair of variables of an integer type plus 0 of that type,
  * splits for inequality between these variables
  * and reconstructs the subproblems with a (nested) if-then-else.
  *
  * Takes into account knowledge about equality/inequality in the path condition.
  *
  */
case object InequalitySplit extends Rule("Ineq. Split.") {

  // Represents NEGATIVE knowledge
  private abstract class Fact {
    val l: Expr
    val r: Expr
  }
  private case class LT(l: Expr, r: Expr) extends Fact
  private case class EQ(l: Expr, r: Expr) extends Fact

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    val TopLevelAnds(as) = and(p.pc, p.phi)

    def getFacts(e: Expr): Set[Fact] = e match {
      case LessThan(a, b)           => Set(LT(b,a), EQ(a,b))
      case LessEquals(a, b)         => Set(LT(b,a))
      case GreaterThan(a, b)        => Set(LT(a,b), EQ(a,b))
      case GreaterEquals(a, b)      => Set(LT(a,b))
      case Equals(a, b)             => Set(LT(a,b), LT(b,a))
      case Not(LessThan(a, b))      => Set(LT(a,b))
      case Not(LessEquals(a, b))    => Set(LT(a,b), EQ(a,b))
      case Not(GreaterThan(a, b))   => Set(LT(b,a))
      case Not(GreaterEquals(a, b)) => Set(LT(b,a), EQ(a,b))
      case Not(Equals(a, b))        => Set(EQ(a,b))
      case _ => Set()
    }

    val facts = as flatMap getFacts

    val candidates =
      (p.as.map(_.toVariable).filter(_.getType == Int32Type) :+ IntLiteral(0)).combinations(2).toList ++
      (p.as.map(_.toVariable).filter(_.getType == IntegerType) :+ InfiniteIntegerLiteral(0)).combinations(2).toList

    candidates.flatMap {
      case List(v1, v2) =>

        val lt = if (!facts.contains(LT(v1, v2))) {
          val pc = LessThan(v1, v2)
          Some(pc, p.copy(pc = and(p.pc, pc), eb = p.qeb.filterIns(pc)))
        } else None

        val gt = if (!facts.contains(LT(v2, v1))) {
          val pc = GreaterThan(v1, v2)
          Some(pc, p.copy(pc = and(p.pc, pc), eb = p.qeb.filterIns(pc)))
        } else None

        val eq = if (!facts.contains(EQ(v1, v2)) && !facts.contains(EQ(v2,v1))) {
          val pc = Equals(v1, v2)
          // One of v1, v2 will be an input variable
          val a1 = (v1, v2) match {
            case (Variable(a), _) => a
            case (_, Variable(a)) => a
          }
          val newP = p.copy(
            as = p.as.diff(Seq(a1)),
            pc = subst(a1 -> v2, p.pc),
            ws = subst(a1 -> v2, p.ws),
            phi = subst(a1 -> v2, p.phi),
            eb = p.qeb.filterIns(Equals(v1, v2)).removeIns(Set(a1))
          )
          Some(pc, newP)
        } else None

        val (pcs, subProblems) = List(eq, lt, gt).flatten.unzip

        if (pcs.size < 2) None
        else {

          val onSuccess: List[Solution] => Option[Solution] = { sols =>
            val pre = orJoin(pcs.zip(sols).map { case (pc, sol) =>
              and(pc, sol.pre)
            })

            val term = pcs.zip(sols) match {
              case Seq((pc1, s1), (_, s2)) =>
                IfExpr(pc1, s1.term, s2.term)
              case Seq((pc1, s1), (pc2, s2), (_, s3)) =>
                IfExpr(pc1, s1.term, IfExpr(pc2, s2.term, s3.term))
            }

            Some(Solution(pre, sols.flatMap(_.defs).toSet, term, sols.forall(_.isTrusted)))
          }

          Some(decomp(subProblems, onSuccess, s"Ineq. Split on '$v1' and '$v2'"))
        }
    }
  }
}
