package sutd.compiler

import sutd.compiler.LambdaCalculus.*
import sutd.compiler.Monad.*
import sutd.compiler.StateT.*
import sutd.compiler.Util.*


object AlgorithmW {
    import Term.* 
    import Value.* 
    import Var.* 
    import Op.* 

    enum Type {
        case IntTy                   // int
        case BoolTy                  // bool
        case FunTy(t1:Type, t2:Type) // t1 -> t2
        case VarTy(alpha:String)     // alpha 
    }


    // type scheme sigma
    enum TypeScheme {
        case Simple(t:Type) // T
        case Forall(alpha:String, sig:TypeScheme) // forall alpha. sig
    }

    // type environment Gamma
    type Gamma = Map[Var, TypeScheme]

    // Type Substitution Psi
    enum TypeSubst {
        case Empty // []
        case Single(alpha:String, t:Type) // [t/alpha]
        case Compo(psi2:TypeSubst, psi1:TypeSubst) // psi2 o psi1
    }

    import TypeSubst.*
    // compo with simplification
    def compo(psi2:TypeSubst, psi1:TypeSubst):TypeSubst = (psi2, psi1) match {
        case (Empty, _) => psi1
        case (_, Empty) => psi2
        case (_, _) => Compo(psi2, psi1)
    }

    trait FTV[A] {
        def ftv(a:A):Set[String]
    }

    import Type.*
    import TypeScheme.*

    
    /**
      * ftv for type scheme
      * 
      * ftv(forall alpha.sigma) = ftv(sigma) - {alpha}
      * 
      */
    given tsFTV:FTV[TypeScheme] = new FTV[TypeScheme] {
        def ftv(sig:TypeScheme):Set[String] = sig match {
            case Simple(ty) => typeFTV.ftv(ty) 
            case Forall(alpha, sig) => ftv(sig) - alpha
        } 
    }

    /**
      * ftv for type
      * 
      * ftv(alpha) = {alpha} 
      * ftv(int) = {}
      * ftv(bool) = {}
      * ftv(T1 -> T2) = ftv(T1) U ftv(T2)
      */
    given typeFTV:FTV[Type] = new FTV[Type] {
        def ftv(ty:Type):Set[String] = ty match {
            case IntTy => Set()
            case BoolTy => Set() 
            case FunTy(t1,t2) => ftv(t1) union ftv(t2)
            case VarTy(alpha) => Set(alpha)
        }
    }

    /**
      * ftv for type environment
      * 
      * ftv(Gamma) = { alpha | (x, sigma) \in Gamma and alpha in ftv(sigma) }
      */
    given gammaFTV:FTV[Gamma] = new FTV[Gamma] {
        def ftv(g:Gamma):Set[String] = g.toList.foldLeft(Set())( (acc, p) => p match {
            case (x, sigma) => acc union tsFTV.ftv(sigma)
        })
    }

    /**
      * Type Subtitution operation
      *     appTySubst applies a type substitution tySubst to an `a` of type A
      */
    trait TypeSubstitutable[A] {
        def appTySubst(tySubst:TypeSubst,a:A)(using m:StateResultMonadError[StateInfo]):StateResult[A] 
    }
    
    /**
      * Applying Type Substiution to Types 
      * 
      * []T = T    (duplicate from the type scheme rule)
      * (Psi o Psi2)T =  Psi1(Psi2(T))  (duplicate from the type scheme rule)
      * [T/alpha]int = int
      * [T/alpha]bool = bool
      * [T/alpha]alpha = T
      * [T/alpha]beta = beta     if beta != alpha
      * [T/alpha]T1 -> T2 = ([T/alpha]T1) -> ([T/alpha]T2)
      * 
      */
    given tyTypeSubst:TypeSubstitutable[Type] = new TypeSubstitutable[Type] {
        def appTySubst(tySubst:TypeSubst, ty:Type)(using m:StateResultMonadError[StateInfo]):StateResult[Type] = tySubst match {
            case Empty => m.pure(ty)
            case Compo(psi2, psi1) => for {
                ty1 <- appTySubst(psi1, ty)
                ty2 <- appTySubst(psi2, ty1)
            } yield ty2
            case Single(alpha, ty2) => ty match {
                case BoolTy => m.pure(BoolTy)
                case IntTy => m.pure(IntTy)
                case FunTy(t1,t2) => for {
                    t1p <- appTySubst(tySubst, t1)
                    t2p <- appTySubst(tySubst, t2)
                } yield FunTy(t1p, t2p)
                case VarTy(beta) if alpha == beta => m.pure(ty2) 
                case VarTy(beta) => m.pure(VarTy(beta))
            }
        }
    }

    /**
      * Applying Type Substiution to Type schemes 
      * [] sigma = sigma
      * [T/alpha] \forall beta.sigma = \forall beta.([T/alpha]sigma)   where beta != alpha and beta not in ftv(T)    
      * Psi1 o Psi2(sigma) = Psi1(Psi2(sigma))
      */
    given tsTypeSubst:TypeSubstitutable[TypeScheme] = new TypeSubstitutable[TypeScheme] {
        def appTySubst(tySubst:TypeSubst, sig:TypeScheme)(using m:StateResultMonadError[StateInfo]):StateResult[TypeScheme] = tySubst match {
            case Empty => m.pure(sig)
            case Compo(psi2, psi1) => for {
                sig1 <- appTySubst(psi1, sig)
                sig2 <- appTySubst(psi2, sig1)
            } yield sig2
            case Single(alpha, ty) => sig match { 
                case Forall(beta, sig) if (alpha == beta) || (typeFTV.ftv(ty) contains beta) => for { 
                    // type var name clashing, we perform alpha renaming on the level of type.
                    name <- newName
                    s <- m.pure(Single(beta, VarTy(name)))
                    sigp <- appTySubst(s, sig)
                    sigpp <- appTySubst(tySubst, Forall(name, sigp))
                } yield sigpp
                case Forall(beta, sig) => for {
                    sigp <- appTySubst(tySubst, sig)
                } yield Forall(beta, sigp)
                case Simple(ty) => for {
                    typ <- tyTypeSubst.appTySubst(tySubst, ty)
                } yield Simple(typ)
            }
        }
    }

    /**
      * Applying Type Substiution to Type Environments, Gamma 
      * Psi(Gamma) = {( (x, Psi(sigma)) | (x, sigma) \in Gamma )}
      */
    given gammaTypeSubst:TypeSubstitutable[Gamma] = new TypeSubstitutable[Gamma] {
        def appTySubst(tySubst: TypeSubst, a: Gamma)(using m: StateResultMonadError[StateInfo]): StateResult[Gamma] = for {
            kvs <- traverse( (kv:(Var,TypeScheme)) => kv match { 
                case (x, ts) => for { 
                    tsp <- tsTypeSubst.appTySubst(tySubst, ts)
                } yield (x, tsp)
            }, a.toList)
        } yield kvs.toMap
    }

    import Const.*
    def typeInf(g:Gamma, t:Term)(using m:StateResultMonadError[StateInfo]):StateResult[(Type, TypeSubst)] = t match {
        /**
          * Gamma, t1 |= T1, Psi1    Psi1(Gamma), t2 |= T2, Psi2
          * alpha3 = newVar    Psi3 = mgu(Psi2(T1), T2 -> alpha3 )
          * ----------------------------------------------------- (wApp)
          * Gamma, t1 t2 |= Psi3(alpha3), Psi3 o Psi2 o Psi1
          */
        // Task 3 TODO
        case AppTerm(t1, t2) => m.raiseError("TODO")

        /**
          *  c is an integer
          * ----------------------------- (wInt)
          * Gamma, c |= int, []
          * 
          * 
          *  c \in {true, false}
          * ----------------------------- (wBool)
          * Gamma, c |= bool, []
          */
        case ConstTerm(c) => c match {
            case BoolConst(v) => m.pure(BoolTy, Empty)        
            case IntConst(v) => m.pure(IntTy, Empty)
        }
        // FixTerm in our syntax is FixTerm(t), not AppTerm(Fix, t)
        // We need to treat it as applying "fix" to "t". hence this should combines wApp rule and wFix rule
        // The original (wFix) rule

        /**
          * (fix, forall alpha. (alpha -> alpha)-> alpha)  \in Gamma     inst(forall alpha. (alpha -> alpha)-> alpha)) = T
          * ----------------------------------------------------------------------------------------------------------- (wFix)
          * Gamma, fix |=  T, []
          * 
          * 
          * Now Combined with wApp 
          * 
          * 
          * fix, forall alpha. (alpha -> alpha)-> alpha)  \in Gamma    inst(forall alpha. (alpha -> alpha)-> alpha)) = T1
          * Psi1 = []     Psi1(Gamma), t2 |= T2, Psi2    alpha3 = newVar    Psi3 = mgu(Psi2(T1), T2 -> alpha3)
          * ----------------------------------------------------------------------------------------------------------- (wFixApp)
          * Gamma, fix t2 |= Psi3(alpha3), Psi3 o Psi2 o Psi1
          */
        case FixTerm(t2) => for {
            ty1 <- inst(Forall("alpha", Simple(FunTy(FunTy(VarTy("alpha"), VarTy("alpha")), VarTy("alpha")))))
            psi1 = Empty 
            g1 <- gammaTypeSubst.appTySubst(psi1, g)
            (ty2, psi2) <- typeInf(g1, t2)
            alpha3 <- newName 
            ty1p <- tyTypeSubst.appTySubst(psi2, ty1)
            psi3 <- mgu(ty1p, FunTy(ty2, VarTy(alpha3)))
            ty3  <- tyTypeSubst.appTySubst(psi3, (VarTy(alpha3)))
        } yield (ty3, compo(psi3, compo(psi2, psi1)))
        /**
          * Gamma, t1 |= T1, Psi1      Psi1' = mgu(bool, T1) o Psi1
          * Psi1'(Gamma), t2 |= T2, Psi2     Psi2'(Gamma), t3 |= T3, Psi3
          * Psi4 = mgu(Psi3(T2), Psi2(T3))
          * ------------------------------------------------------------------------- (wIf)
          * Gamma, if t1 then t2 else t3 |= Ps4(Psi3(T2)), Psi4 o Psi3 o Psi2 o Psi1' 
          */
        case IfTerm(t1, t2, t3) => for {
            (ty1, psi1) <- typeInf(g, t1)
            psi1t <- mgu(BoolTy, ty1)
            psi1p = compo(psi1t, psi1)
            g1 <- gammaTypeSubst.appTySubst(psi1p, g)
            (ty2, psi2) <- typeInf(g1, t2)
            (ty3, psi3) <- typeInf(g1, t3)
            ty2p <- tyTypeSubst.appTySubst(psi3, ty2)
            ty3p <- tyTypeSubst.appTySubst(psi2, ty3)
            psi4 <- mgu(ty2p, ty3p)
            ty4  <- tyTypeSubst.appTySubst(psi4, ty2p)
        } yield (ty4, compo(psi4, compo(psi3, compo(psi2, psi1p))))

        /**
          * alpha1 = newVar         Gamma oplus (x, alpha1), t |= T, Psi
          * ------------------------------------------------ (wLam)
          * Gamma, \x. t |= Psi(alpha1 -> T), Psi
          */
        case LambdaTerm(x, body) if g.contains(x) => for { // x is already in Gamma, need to alpha rename x first
            n  <- newName
            z  <- m.pure(Var(n))
            s  <- m.pure((x,VarTerm(z))) // [z/y]
            bodyp <- appSubst(s, body) // alpha renaming
            (ty,psi) <- typeInf(g, LambdaTerm(z, bodyp))
        } yield (ty,psi)
        case LambdaTerm(x, body) => for {
            name <- newName
            alpha1 = VarTy(name)
            g1 = g + (x -> Simple(alpha1))
            (ty2, psi) <- typeInf(g1, body)
            ty <- tyTypeSubst.appTySubst(psi, FunTy(alpha1, ty2))
        } yield (ty, psi)
        /**
          * Gamma, t1 |= T1, Psi1       Psi1(Gamma) oplus (x, gen(Psi1(Gamma), T1)), t2 |= T2, Psi2
          * ----------------------------------------------------- (wLet)
          * Gamma, let x = t1 in t2 |= T2, Psi2 o Psi1
          */
        case LetTerm(x, t1, t2) if g.contains(x) => for {  // x is already in Gamma, need to alpha rename x first
            n  <- newName
            z  <- m.pure(Var(n))
            s  <- m.pure((x,VarTerm(z))) // [z/y]
            t2p <- appSubst(s, t2) // alpha renaming
            (ty,psi) <- typeInf(g, LetTerm(z, t1, t2p))
        } yield (ty, psi)
        // Task 3 TODO
        case LetTerm(x, t1, t2) => m.raiseError("TODO")
        /**
          * Gamma, t1 |= T1, Psi1     Psi1(Gamma), t2 |= T2, Psi2
          * Psi3 = mgu(Psi2(T1), T2)
          * --------------------------------------------- (wOp2)
          * Gamma, t1 == t2 |= bool, Psi3 o Psi2 o Psi1
          */
        case OpTerm(t1, DEqual, t2) => for {
            (ty1, psi1) <- typeInf(g, t1)
            g1 <- gammaTypeSubst.appTySubst(psi1, g) 
            (ty2, psi2) <- typeInf(g1, t2)
            ty1p <- tyTypeSubst.appTySubst(psi2, ty1)
            psi3 <- mgu(ty1p, ty2)
        } yield (BoolTy, compo(psi3, compo(psi2, psi1)))
        /**
          * op \in {+, -, *, /}
          * Gamma, t1 |= T1, Psi1     Psi1(Gamma), t2 |= T2, Psi2
          * Psi3 = mgu(Psi2(T1), T2, int)
          * --------------------------------------------- (wOp1)
          * Gamma, t1 op t2 |= int, Psi3 o Psi2 o Psi1
          */        
        case OpTerm(t1, op, t2) => for { 
            (ty1, psi1) <- typeInf(g, t1)
            g1 <- gammaTypeSubst.appTySubst(psi1, g) 
            (ty2, psi2) <- typeInf(g1, t2)
            ty1p <- tyTypeSubst.appTySubst(psi2, ty1)
            psi3 <- mgu(ty1p, ty2, IntTy)
        } yield (IntTy, compo(psi3, compo(psi2, psi1)))

        /**
          * (x, sigma) \in Gamma,   inst(sigma) = T
          * ------------------------------------------------ (wVar)
          * Gamma, x |= T, []
          */
        case VarTerm(x) => g.get(x) match {
            case None => m.raiseError(s"type inference failed. ${x} is undefined.")
            case Some(ts) => for {
                ty <- inst(ts)
            } yield (ty,Empty)
        }
    }

    /**
      * Type scheme instantiation
      *
      * @param ts
      * @param m
      * @return
      */
    def inst(ts:TypeScheme)(using m:StateResultMonadError[StateInfo]):StateResult[Type] = ts match {
        /**
          * [beta/alpha](inst(sig))  where beta = newVar
          */
        case Forall(alpha, sig) => for {
            name <- newName 
            beta = VarTy(name)
            s = Single(alpha, beta)
            sigp <- tsTypeSubst.appTySubst(s, sig)
            t <- inst(sigp)
        } yield t
        /**
          * inst(T) = T
          */
        case Simple(t) => m.pure(t)
    }

    /**
      * Type generalization
      * 
      * gen(Gamma, T) = forall \bar{alpha}. T    where \bar{alpha} = ftv(T) - ftv(Gamma)
      *
      * @param g
      * @param ty
      * @return
      */
    def gen(g:Gamma, ty:Type):TypeScheme = {
        val freeVars = (typeFTV.ftv(ty) diff (gammaFTV.ftv(g))).toList
        freeVars.foldLeft(Simple(ty))( (acc,x) => Forall(x,acc))
    }

    /**
      * most general unifier
      * mgu(alpha, T) = [T/alpha]
      * mgu(T, alpha) = [T/alpha]
      * mgu(int, int) = []
      * mgu(bool, bool) = []
      * mgu(T1 -> T2, T3 -> T4) = let Psi1 = mgu(T1, T3)
      *                               Psi2 = mgu(Psi1(T2), Psi1(T4))
      *                           in Psi2 o Psi1
      *
      * @param ty1
      * @param ty2
      * @param m
      * @return
      */
    def mgu(ty1:Type, ty2:Type)(using m:StateResultMonadError[StateInfo]):StateResult[TypeSubst] = (ty1, ty2) match {
        case (VarTy(alpha), _) => m.pure(Single(alpha, ty2))
        // Task 2 TODO
        // More cases should be added.
        case (_, _) => m.raiseError(s"unification failed. Can't unify ${ty1} with ${ty2}.")
    }

    /**
      * mgu(T1,T2,T3) = let psi1 = mgu(T1,T2)
      *                     psi2 = mgu(psi1(T2), psi1(T3))
      *                 in psi2 o psi1
      * @param ty1
      * @param ty2
      * @param ty3
      * @param m
      * @return
      */
    def mgu(ty1:Type, ty2:Type, ty3:Type)(using m:StateResultMonadError[StateInfo]):StateResult[TypeSubst] = for {
        psi1 <- mgu(ty1, ty2)
        ty2p <- tyTypeSubst.appTySubst(psi1, ty2)
        ty3p <- tyTypeSubst.appTySubst(psi1, ty3)
        psi2 <- mgu(ty2p, ty3p)
    } yield compo(psi2, psi1)

}