/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Types._

import codegen._
import codegen.runtime.{StdMonitor, Monitor}

class DualEvaluator(ctx: LeonContext, prog: Program, params: CodeGenParams)
  extends RecursiveEvaluator(ctx, prog, params.maxFunctionInvocations)
  with HasDefaultGlobalContext {

  type RC = DualRecContext
  def initRC(mappings: Map[Identifier, Expr]): RC = DualRecContext(mappings)
  implicit val debugSection = utils.DebugSectionEvaluation

  val unit = new CompilationUnit(ctx, prog, params)

  var monitor: Monitor = new StdMonitor(unit, params.maxFunctionInvocations, Map())

  val isCompiled = prog.definedFunctions.toSet

  case class DualRecContext(mappings: Map[Identifier, Expr], needJVMRef: Boolean = false) extends RecContext[DualRecContext] {
    def newVars(news: Map[Identifier, Expr]) = copy(news)
  }

  case class RawObject(o: AnyRef, tpe: TypeTree) extends Expr {
    val getType = tpe
  }

  def call(tfd: TypedFunDef, args: Seq[AnyRef]): Expr = {

    val (className, methodName, _) = unit.leonFunDefToJVMInfo(tfd.fd).get

    val allArgs = Seq(monitor) ++
      (if (tfd.fd.tparams.nonEmpty) Seq(tfd.tps.map(unit.registerType(_)).toArray) else Seq()) ++
      args

    ctx.reporter.debug(s"Calling $className.$methodName(${args.mkString(",")})")

    try {
      val cl = unit.loader.loadClass(className)

      val meth = cl.getMethods.find(_.getName == methodName).get

      val res = if (allArgs.isEmpty) {
        meth.invoke(null)
      } else {
        meth.invoke(null, allArgs : _*)
      }

      RawObject(res, tfd.returnType)
    } catch {
      case e: java.lang.reflect.InvocationTargetException =>
        throw new RuntimeError(e.getCause.getMessage)

      case t: Throwable =>
        t.printStackTrace()
        throw new EvalError(t.getMessage)
    }
  }

  def retrieveField(fd : FunDef): Expr = {

    val (className, fieldName, _) = unit.leonFunDefToJVMInfo(fd).get

    ctx.reporter.debug(s"Retrieving $className.$fieldName")

    try {
      val cl = unit.loader.loadClass(className)

      val field = cl.getFields.find(_.getName == fieldName).get

      val res = field.get(null)

      RawObject(res, fd.returnType)
    } catch {
      case e: java.lang.reflect.InvocationTargetException =>
        throw new RuntimeError(e.getCause.getMessage)

      case t: Throwable =>
        t.printStackTrace()
        throw new EvalError(t.getMessage)
    }
  }
  
  
  
  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case FunctionInvocation(tfd, args) =>
      if (isCompiled(tfd.fd)) {
        if (!tfd.fd.canBeStrictField) {
          val rargs = args.map(
            e(_)(rctx.copy(needJVMRef = true), gctx) match {
              case RawObject(obj, _) => obj
              case _ => throw new EvalError("Failed to get JVM ref when requested")
            }
          )
  
          jvmBarrier(call(tfd, rargs), rctx.needJVMRef)
        } else {
          jvmBarrier(retrieveField(tfd.fd), rctx.needJVMRef)
        }
      } else {
        jvmBarrier(super.e(expr)(rctx.copy(needJVMRef = false), gctx), rctx.needJVMRef)
      }
    case _ =>
      jvmBarrier(super.e(expr)(rctx.copy(needJVMRef = false), gctx), rctx.needJVMRef)
  }

  def jvmBarrier(e: Expr, returnJVMRef: Boolean): Expr = {
    e match {
      case RawObject(obj, _) if returnJVMRef =>
        e
      case RawObject(obj, _) if !returnJVMRef =>
        unit.jvmToValue(obj, e.getType)
      case e              if returnJVMRef =>
        RawObject(unit.valueToJVM(e)(monitor), e.getType)
      case e              if !returnJVMRef =>
        e
    }
  }

  override def eval(ex: Expr, model: solvers.Model) = {
    monitor = unit.getMonitor(model, params.maxFunctionInvocations)
    super.eval(ex, model)
  }

}
