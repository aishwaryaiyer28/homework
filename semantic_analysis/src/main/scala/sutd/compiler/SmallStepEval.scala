package sutd.compiler

import sutd.compiler.LambdaCalculus.*
import sutd.compiler.Util.*
import sutd.compiler.Monad.*
import sutd.compiler.StateT.*


object SmallStepEval {
    import StateInfo.*
    import Term.*
    import Value.*
    import Const.*

    /**
      * implementing small step operational semantics for lambda calculus
      *
      * @param t - a lambda calculus term
      * @param m - the StateResultMonadError dictionary with all the monad error API
      * @return - stateful result which is either an error message or a term
      */
    def eval_one_step(t:Term)(using m:StateResultMonadError[StateInfo]):StateResult[Term] = t match {
      case AppTerm(LambdaTerm(x, t1), t2) => for {
        t3 <- appSubst((x, t2), t1)
      } yield t3
      case AppTerm(t1, t2) => for {
        t3 <- eval_one_step(t1)
      } yield AppTerm(t3, t2)
      case ConstTerm(c) => m.pure(t)
      // Task 1 TODO
      case FixTerm(t) => m.raiseError("TODO") 
      // Task 1 TODO
      case IfTerm(t1, t2, t3) => m.raiseError("TODO")
      case LambdaTerm(x, body) => m.pure(t) 
      case LetTerm(x, t1, t2) => for {
        t3 <- appSubst((x, t1),t2)
      } yield t3
      case OpTerm(ConstTerm(IntConst(i)), Op.Plus, ConstTerm(IntConst(j)))     => m.pure(ConstTerm(IntConst(i + j)))
      case OpTerm(ConstTerm(IntConst(i)), Op.Minus, ConstTerm(IntConst(j)))    => m.pure(ConstTerm(IntConst(i - j)))
      case OpTerm(ConstTerm(IntConst(i)), Op.Mult, ConstTerm(IntConst(j)))     => m.pure(ConstTerm(IntConst(i * j)))
      case OpTerm(ConstTerm(IntConst(i)), Op.Div, ConstTerm(IntConst(0)))      => m.raiseError(s"division by zero error.")
      case OpTerm(ConstTerm(IntConst(i)), Op.Div, ConstTerm(IntConst(j)))      => m.pure(ConstTerm(IntConst(i / j)))
      case OpTerm(ConstTerm(IntConst(i)), Op.DEqual, ConstTerm(IntConst(j)))   => m.pure(ConstTerm(BoolConst(i == j)))
      case OpTerm(ConstTerm(BoolConst(i)), Op.DEqual, ConstTerm(BoolConst(j))) => m.pure(ConstTerm(BoolConst(i == j)))
      case OpTerm(ConstTerm(BoolConst(i)), _, ConstTerm(BoolConst(j)))         => m.raiseError(s"type error.")
      case OpTerm(ConstTerm(c1), op, t2) => for {
        t3 <- eval_one_step(t2) 
      } yield OpTerm(ConstTerm(c1), op, t3)
      case OpTerm(t1, op, t2) => for {
        t3 <- eval_one_step(t1) 
      } yield OpTerm(t3, op, t2)
      case VarTerm(x) => m.pure(t)
    }

    def eval(t:Term)(using m:StateResultMonadError[StateInfo]):StateResult[Value] = for { 
      t1 <- eval_one_step(t)
      t2 <- t1 match {
        case ConstTerm(c) => m.pure(ConstValue(c))
        case _ if t1 == t => m.raiseError(s"evaluation is stucked.")
        case _ => eval(t1)
      }
    } yield t2 
}