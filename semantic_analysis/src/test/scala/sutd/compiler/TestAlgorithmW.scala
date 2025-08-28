package sutd.compiler

import scala.language.adhocExtensions
import org.scalatest.funsuite
import org.scalatest.matchers
import sutd.compiler.LambdaCalculus.* 
import sutd.compiler.Util.*
import sutd.compiler.AlgorithmW.*

class TestAlgorithmW extends funsuite.AnyFunSuite {
    import Term.* 
    import Value.*
    import Const.* 
    import Op.*
    import Result.* 
    import Type.*
    import TypeScheme.*

    val st = StateInfo(0)

    test("test mgu: int and int can be unified") {
        val ty1 = IntTy
        val ty2 = IntTy 
        val expected = TypeSubst.Empty
        mgu(ty1, ty2).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_, result) => assert(result == expected)
        }
    }

    test("test mgu: int and bool cannot be unified") {        
        val ty1 = IntTy
        val ty2 = BoolTy 
        val expected = TypeSubst.Empty
        mgu(ty1, ty2).run(st) match {
            case Error(err) => assert(true)
            case Ok(_, result) => assert(false, s"int and bool can't be unified but a result is returend ${result}")
        }
    }

    test("test mgu: int and alpha can be unified") {
        val ty1 = IntTy
        val ty2 = VarTy("a") 
        val expected = TypeSubst.Single("a", IntTy)
        mgu(ty1, ty2).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_, result) => assert(result == expected)
        }
    }

    test("test mgu: int -> alpha and alpha -> int can be unified") {
        val ty1 = FunTy(IntTy,VarTy("a"))
        val ty2 = FunTy(VarTy("a"),IntTy) 
        val expected = TypeSubst.Single("a", IntTy)
        mgu(ty1, ty2).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_, result) => assert(result == expected)
        }
    }

    test("test algo W: one has type int") {
        val t = ConstTerm(IntConst(1))
        val g = Map[Var, TypeScheme]()
        val expected = IntTy 

        typeInf(g,t).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_,(ty,psi)) => assert(ty == expected)
        }
    }

    test("test algo W: \\x.x has type alpha -> alpha ") {
        val id = LambdaTerm(Var("x"), VarTerm(Var("x"))) // \x.x 
        val g = Map[Var, TypeScheme]()
        val expected = FunTy(VarTy("_x_0"),VarTy("_x_0"))

        typeInf(g,id).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_,(ty,psi)) => 
                assert(ty == expected)
        }
    }

    test("test algo W: fix \\f.\\x. if x == 0 then 1 else x * (f (x-1)) has type int => int") {
        val three = IntConst(3)
        val zero = IntConst(0)
        val one = IntConst(1)
        val varx = Var("x")
        val varf = Var("f")
        val cond = OpTerm(VarTerm(varx), DEqual, ConstTerm(zero)) // x == 0
        val ifelse = IfTerm(cond, ConstTerm(one), OpTerm(VarTerm(varx), Mult, AppTerm(VarTerm(varf), OpTerm(VarTerm(varx), Minus, ConstTerm(one))))) // if x == 0 then 1 else x * (f (x-1))
        val fac = FixTerm(LambdaTerm(varf, LambdaTerm(varx, ifelse)))  // fix \f.\x. if x == 0 then 1 else x * (f (x-1))
        val g = Map[Var, TypeScheme]()
        val expected = FunTy(IntTy,IntTy)

        typeInf(g,fac).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_,(ty,psi)) => 
                assert(ty == expected)
        }
    }

    test("test algo W: let f=\\x.x in (let g=\\x.\\y.x in g (f 1) (f true)) has type int") {
        val one = IntConst(1)
        val tt = BoolConst(true)
        val varx = Var("x")
        val vary = Var("y")
        val varf = Var("f")
        val varg = Var("g")
        val id = LambdaTerm(varx, VarTerm(varx)) // \x.x 
        val fst = LambdaTerm(varx, LambdaTerm(vary, VarTerm(varx)))
        val t = LetTerm(varf, id,
            LetTerm(varg, fst, 
                AppTerm(AppTerm(VarTerm(varg), 
                            AppTerm(VarTerm(varf), ConstTerm(one))), 
                    (AppTerm(VarTerm(varf), ConstTerm(tt))))
            ) 
        )
        val g = Map[Var, TypeScheme]()
        val expected = IntTy

        typeInf(g,t).run(st) match {
            case Error(err) => assert(false, err)
            case Ok(_,(ty,psi)) => 
                assert(ty == expected)
        }
    }

}