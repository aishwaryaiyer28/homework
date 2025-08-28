file://<WORKSPACE>/src/main/scala/sutd/compiler/Util.scala
### java.lang.AssertionError: assertion failed: tree: StringFormat[A](null:
  (sutd.compiler.Util.resultMonadError :
    sutd.compiler.Monad.MonadError[sutd.compiler.Util.Result,
      sutd.compiler.Util.Err]
  )
), pt: <notype>

occurred in the presentation compiler.

presentation compiler configuration:
Scala version: 3.3.3
Classpath:
<HOME>/Library/Caches/Coursier/v1/https/repo1.maven.org/maven2/org/scala-lang/scala3-library_3/3.3.3/scala3-library_3-3.3.3.jar [exists ], <HOME>/Library/Caches/Coursier/v1/https/repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.12/scala-library-2.13.12.jar [exists ]
Options:



action parameters:
uri: file://<WORKSPACE>/src/main/scala/sutd/compiler/Util.scala
text:
```scala
package sutd.compiler

import sutd.compiler.LambdaCalculus.*
import sutd.compiler.Monad.*
import sutd.compiler.StateT.*


object Util {
    import Term.* 
    import Value.*
    // A substitution 
    type Subst = (Var,Term) 

    type Err = String

    case class StateInfo(nextNum:Int)

    enum Result[+A] {
        case Error(msg:String) extends Result[A]
        case Ok[A](result:A) extends Result[A]
    }


    given resultMonadError: MonadError[Result, Err] = 
        new MonadError[Result, String] {
            override def bind[A, B](fa: Result[A])(f: A => Result[B]): Result[B] = fa match {
                case Result.Ok(a)    => f(a)
                case Result.Error(s) => Result.Error(s)
            }

            override def pure[A](x: A): Result[A] = Result.Ok(x)
            override def raiseError[A](e:String):Result[A] = Result.Error(e)
            override def handleErrorWith[A](fa: Result[A])(f:Err => Result[A]) : Result[A] = fa match {
                case Result.Error(s) => f(s)
                case Result.Ok(a)    => Result.Ok(a)
            }
        }

    
    trait StateResultMonadError[S] extends StateTMonadError[S, Result, Err] { 
        override def M0 = resultMonadError
        override def raiseError[A](e:Err):StateT[S,Result,A] = {
            StateT(st => Result.Error(e))
        }
        override def handleErrorWith[A](fa:StateT[S,Result,A])(f:Err => StateT[S,Result,A]): StateT[S,Result,A] = {
            StateT(st => fa.run(st) match {
                case Result.Error(s) => f(s).run(st)
                case Result.Ok(a)    => Result.Ok(a)
            })
        }
    }

    given stateResultMonadError[S]:StateResultMonadError[S] = new StateResultMonadError[S]{}


    def get: StateT[StateInfo, Result, StateInfo] = StateT{ st => Result.Ok(st, st) }
    def put(st:StateInfo): StateT[StateInfo, Result, Unit] = StateT{ _ => Result.Ok(st, ())}

    type StateResult[A] = StateT[StateInfo, Result, A]

    /** 
     * issue a new name and increment the nextNum in the state
     * */

    def newName:StateResult[String] = for {
        st <- get
        _  <- put(st.copy(nextNum= st.nextNum+1))
    } yield (s"_x_${st.nextNum}")
    

    /**
      * apply substituion s to lambda calculus term t
      *
      * @param s substitution
      * @param t lambda term
      * @param m StateResultMonad dictionary containing all the Monad api
      * @return a StateResult, containing Result[StateInfo,Term]
      */
    def appSubst(s:Subst, t:Term)(using m:StateResultMonadError[StateInfo]):StateResult[Term] = t match {
        case ConstTerm(c) => m.pure(ConstTerm(c))
        case VarTerm(y)   => s match {
            case (x,u) if y == x => m.pure(u)
            case (x,u) => m.pure(VarTerm(y))
        }
        case AppTerm(t1,t2) => for { 
            t3 <- appSubst(s, t1)
            t4 <- appSubst(s, t2)
        } yield AppTerm(t3,t4)
        case IfTerm(t1, t2, t3) => for {
            t4 <- appSubst(s, t1)
            t5 <- appSubst(s, t2)
            t6 <- appSubst(s, t3)
        } yield IfTerm(t4,t5,t6)
        case LetTerm(y, t2,t3) => s match {
            case (x, t1) if ((y !=x) && !(fv(t1).contains(y))) => for {
                t4 <- appSubst(s, t2)
                t5 <- appSubst(s, t3)
            } yield LetTerm(y, t4, t5)
            case (x, t1) => for {
                /* Substitution Application would fail because let bound variable is clashing with the substitution domain. 
                 * or substitution domain is captured in the RHS of let binding. 
                 * instead of failing, we apply alpha renaming to y and t3 immediately
                 * */ 
                n   <- newName
                z   <- m.pure(Var(n))
                s2  <- m.pure((y,VarTerm(z))) // [z/y]
                t3p <- appSubst(s2, t3) // alpha renaming
                t4  <- appSubst(s, t2)  // subst after alpha renaming
                t5  <- appSubst(s, t3p) // subst after alpha renaming
            } yield LetTerm(z, t4, t5)
        }
        case LambdaTerm(y, t2) => s match {
            case (x,t1) if ((y != x) && !(fv(t1).contains(y))) => for {
                t3 <- appSubst(s, t2)
            } yield LambdaTerm(y, t3)
            case (x, t1) => for {
                /* Substitution Application would fail because lambda bound variable is clashing with the substitution domain. 
                 * or substitution domain is captured in the body of lambda abstraction. 
                 * instead of failing, we apply alpha renaming to y and t2 immediately
                 * */ 
                n   <- newName
                z   <- m.pure(Var(n))
                s2  <- m.pure((y,VarTerm(z))) // [z/y]
                t2p <- appSubst(s2, t2) // alpha renaming
                t3  <- appSubst(s, t2p) // subst after alpha renaming
            } yield LambdaTerm(z, t3)
        } 
        case FixTerm(t) =>  for {
            tp <- appSubst(s, t)
        } yield FixTerm(tp)

        case OpTerm(t1, op, t2) => for {
            tp1 <- appSubst(s, t1) 
            tp2 <- appSubst(s, t2) 
        } yield OpTerm(tp1, op, tp2)

    }

}
```



#### Error stacktrace:

```
scala.runtime.Scala3RunTime$.assertFailed(Scala3RunTime.scala:8)
	dotty.tools.dotc.typer.Typer.adapt1(Typer.scala:3598)
	dotty.tools.dotc.typer.Typer.adapt(Typer.scala:3590)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Implicits.tryConversion$1(Implicits.scala:1137)
	dotty.tools.dotc.typer.Implicits.typedImplicit(Implicits.scala:1168)
	dotty.tools.dotc.typer.Implicits.typedImplicit$(Implicits.scala:819)
	dotty.tools.dotc.typer.Typer.typedImplicit(Typer.scala:117)
	dotty.tools.dotc.typer.Implicits$ImplicitSearch.tryImplicit(Implicits.scala:1243)
	dotty.tools.dotc.typer.Implicits$ImplicitSearch.rank$1(Implicits.scala:1342)
	dotty.tools.dotc.typer.Implicits$ImplicitSearch.searchImplicit(Implicits.scala:1512)
	dotty.tools.dotc.typer.Implicits$ImplicitSearch.searchImplicit(Implicits.scala:1540)
	dotty.tools.dotc.typer.Implicits$ImplicitSearch.bestImplicit(Implicits.scala:1573)
	dotty.tools.dotc.typer.Implicits.inferImplicit(Implicits.scala:1061)
	dotty.tools.dotc.typer.Implicits.inferImplicit$(Implicits.scala:819)
	dotty.tools.dotc.typer.Typer.inferImplicit(Typer.scala:117)
	dotty.tools.dotc.typer.Implicits.inferView(Implicits.scala:857)
	dotty.tools.dotc.typer.Implicits.inferView$(Implicits.scala:819)
	dotty.tools.dotc.typer.Typer.inferView(Typer.scala:117)
	dotty.tools.dotc.typer.Implicits.viewExists(Implicits.scala:832)
	dotty.tools.dotc.typer.Implicits.viewExists$(Implicits.scala:819)
	dotty.tools.dotc.typer.Typer.viewExists(Typer.scala:117)
	dotty.tools.dotc.typer.Implicits.ignoredConvertibleImplicits$1$$anonfun$3(Implicits.scala:961)
	scala.collection.Iterator$$anon$6.hasNext(Iterator.scala:479)
	scala.collection.Iterator.isEmpty(Iterator.scala:466)
	scala.collection.Iterator.isEmpty$(Iterator.scala:466)
	scala.collection.AbstractIterator.isEmpty(Iterator.scala:1300)
	scala.collection.View$Filter.isEmpty(View.scala:146)
	scala.collection.IterableOnceOps.nonEmpty(IterableOnce.scala:853)
	scala.collection.IterableOnceOps.nonEmpty$(IterableOnce.scala:853)
	scala.collection.AbstractIterable.nonEmpty(Iterable.scala:933)
	dotty.tools.dotc.reporting.MissingImplicitArgument.noChainConversionsNote$1(messages.scala:2929)
	dotty.tools.dotc.reporting.MissingImplicitArgument.msgPostscript$$anonfun$4(messages.scala:2944)
	scala.Option.orElse(Option.scala:477)
	dotty.tools.dotc.reporting.MissingImplicitArgument.msgPostscript(messages.scala:2944)
	dotty.tools.dotc.reporting.Message.message$$anonfun$1(Message.scala:344)
	dotty.tools.dotc.reporting.Message.inMessageContext(Message.scala:340)
	dotty.tools.dotc.reporting.Message.message(Message.scala:344)
	dotty.tools.dotc.reporting.Message.isNonSensical(Message.scala:321)
	dotty.tools.dotc.reporting.HideNonSensicalMessages.isHidden(HideNonSensicalMessages.scala:16)
	dotty.tools.dotc.reporting.HideNonSensicalMessages.isHidden$(HideNonSensicalMessages.scala:10)
	dotty.tools.dotc.interactive.InteractiveDriver$$anon$5.isHidden(InteractiveDriver.scala:156)
	dotty.tools.dotc.reporting.Reporter.issueUnconfigured(Reporter.scala:156)
	dotty.tools.dotc.reporting.Reporter.go$1(Reporter.scala:181)
	dotty.tools.dotc.reporting.Reporter.issueIfNotSuppressed(Reporter.scala:200)
	dotty.tools.dotc.reporting.Reporter.report(Reporter.scala:203)
	dotty.tools.dotc.reporting.StoreReporter.report(StoreReporter.scala:50)
	dotty.tools.dotc.report$.error(report.scala:68)
	dotty.tools.dotc.typer.Typer.issueErrors$1$$anonfun$1(Typer.scala:3811)
	scala.runtime.function.JProcedure3.apply(JProcedure3.java:15)
	scala.runtime.function.JProcedure3.apply(JProcedure3.java:10)
	scala.collection.LazyZip3.foreach(LazyZipOps.scala:248)
	dotty.tools.dotc.typer.Typer.issueErrors$1(Typer.scala:3813)
	dotty.tools.dotc.typer.Typer.addImplicitArgs$1(Typer.scala:3835)
	dotty.tools.dotc.typer.Typer.adaptNoArgsImplicitMethod$1(Typer.scala:3852)
	dotty.tools.dotc.typer.Typer.adaptNoArgs$1(Typer.scala:4047)
	dotty.tools.dotc.typer.Typer.adapt1(Typer.scala:4277)
	dotty.tools.dotc.typer.Typer.adapt(Typer.scala:3590)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3191)
	dotty.tools.dotc.typer.Typer.typedExpr(Typer.scala:3303)
	dotty.tools.dotc.typer.Typer.typedBlock(Typer.scala:1168)
	dotty.tools.dotc.typer.Typer.typedUnnamed$1(Typer.scala:3058)
	dotty.tools.dotc.typer.Typer.typedUnadapted(Typer.scala:3115)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3191)
	dotty.tools.dotc.typer.Typer.typedExpr(Typer.scala:3303)
	dotty.tools.dotc.typer.Typer.$anonfun$57(Typer.scala:2486)
	dotty.tools.dotc.inlines.PrepareInlineable$.dropInlineIfError(PrepareInlineable.scala:243)
	dotty.tools.dotc.typer.Typer.typedDefDef(Typer.scala:2486)
	dotty.tools.dotc.typer.Typer.typedNamed$1(Typer.scala:3026)
	dotty.tools.dotc.typer.Typer.typedUnadapted(Typer.scala:3114)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3191)
	dotty.tools.dotc.typer.Typer.traverse$1(Typer.scala:3213)
	dotty.tools.dotc.typer.Typer.typedStats(Typer.scala:3259)
	dotty.tools.dotc.typer.Typer.typedClassDef(Typer.scala:2669)
	dotty.tools.dotc.typer.Typer.typedTypeOrClassDef$1(Typer.scala:3038)
	dotty.tools.dotc.typer.Typer.typedNamed$1(Typer.scala:3042)
	dotty.tools.dotc.typer.Typer.typedUnadapted(Typer.scala:3114)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3191)
	dotty.tools.dotc.typer.Typer.traverse$1(Typer.scala:3213)
	dotty.tools.dotc.typer.Typer.typedStats(Typer.scala:3259)
	dotty.tools.dotc.typer.Typer.typedClassDef(Typer.scala:2669)
	dotty.tools.dotc.typer.Typer.typedTypeOrClassDef$1(Typer.scala:3038)
	dotty.tools.dotc.typer.Typer.typedNamed$1(Typer.scala:3042)
	dotty.tools.dotc.typer.Typer.typedUnadapted(Typer.scala:3114)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3191)
	dotty.tools.dotc.typer.Typer.traverse$1(Typer.scala:3213)
	dotty.tools.dotc.typer.Typer.typedStats(Typer.scala:3259)
	dotty.tools.dotc.typer.Typer.typedPackageDef(Typer.scala:2812)
	dotty.tools.dotc.typer.Typer.typedUnnamed$1(Typer.scala:3083)
	dotty.tools.dotc.typer.Typer.typedUnadapted(Typer.scala:3115)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3187)
	dotty.tools.dotc.typer.Typer.typed(Typer.scala:3191)
	dotty.tools.dotc.typer.Typer.typedExpr(Typer.scala:3303)
	dotty.tools.dotc.typer.TyperPhase.typeCheck$$anonfun$1(TyperPhase.scala:44)
	dotty.tools.dotc.typer.TyperPhase.typeCheck$$anonfun$adapted$1(TyperPhase.scala:50)
	scala.Function0.apply$mcV$sp(Function0.scala:42)
	dotty.tools.dotc.core.Phases$Phase.monitor(Phases.scala:440)
	dotty.tools.dotc.typer.TyperPhase.typeCheck(TyperPhase.scala:50)
	dotty.tools.dotc.typer.TyperPhase.runOn$$anonfun$3(TyperPhase.scala:84)
	scala.runtime.function.JProcedure1.apply(JProcedure1.java:15)
	scala.runtime.function.JProcedure1.apply(JProcedure1.java:10)
	scala.collection.immutable.List.foreach(List.scala:333)
	dotty.tools.dotc.typer.TyperPhase.runOn(TyperPhase.scala:84)
	dotty.tools.dotc.Run.runPhases$1$$anonfun$1(Run.scala:246)
	scala.runtime.function.JProcedure1.apply(JProcedure1.java:15)
	scala.runtime.function.JProcedure1.apply(JProcedure1.java:10)
	scala.collection.ArrayOps$.foreach$extension(ArrayOps.scala:1323)
	dotty.tools.dotc.Run.runPhases$1(Run.scala:262)
	dotty.tools.dotc.Run.compileUnits$$anonfun$1(Run.scala:270)
	dotty.tools.dotc.Run.compileUnits$$anonfun$adapted$1(Run.scala:279)
	dotty.tools.dotc.util.Stats$.maybeMonitored(Stats.scala:71)
	dotty.tools.dotc.Run.compileUnits(Run.scala:279)
	dotty.tools.dotc.Run.compileSources(Run.scala:194)
	dotty.tools.dotc.interactive.InteractiveDriver.run(InteractiveDriver.scala:165)
	scala.meta.internal.pc.MetalsDriver.run(MetalsDriver.scala:45)
	scala.meta.internal.pc.WithCompilationUnit.<init>(WithCompilationUnit.scala:28)
	scala.meta.internal.pc.SimpleCollector.<init>(PcCollector.scala:373)
	scala.meta.internal.pc.PcSemanticTokensProvider$Collector$.<init>(PcSemanticTokensProvider.scala:61)
	scala.meta.internal.pc.PcSemanticTokensProvider.Collector$lzyINIT1(PcSemanticTokensProvider.scala:61)
	scala.meta.internal.pc.PcSemanticTokensProvider.Collector(PcSemanticTokensProvider.scala:61)
	scala.meta.internal.pc.PcSemanticTokensProvider.provide(PcSemanticTokensProvider.scala:90)
	scala.meta.internal.pc.ScalaPresentationCompiler.semanticTokens$$anonfun$1(ScalaPresentationCompiler.scala:117)
```
#### Short summary: 

java.lang.AssertionError: assertion failed: tree: StringFormat[A](null:
  (sutd.compiler.Util.resultMonadError :
    sutd.compiler.Monad.MonadError[sutd.compiler.Util.Result,
      sutd.compiler.Util.Err]
  )
), pt: <notype>