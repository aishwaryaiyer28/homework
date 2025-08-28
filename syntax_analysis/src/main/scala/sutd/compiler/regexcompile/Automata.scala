package sutd.compiler.regexcompile


object Automata {
    trait StateMachine[S,L] {
        def step(state:S, symb:L):Option[S]
        def isFinal(state:S):Boolean
    }

    def runStateMachine[S,L](s:S,symbs:List[L])(using machine:StateMachine[S,L]):Boolean = symbs match {
        case Nil => machine.isFinal(s)
        case (l::ls) => {
            machine.step(s,l) match {
                case None    => false
                case Some(t) => runStateMachine(t, ls)

            }
        }
    }
}

