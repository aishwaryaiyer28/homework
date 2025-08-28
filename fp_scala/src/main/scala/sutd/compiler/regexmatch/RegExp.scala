package sutd.compiler.regexmatch

object RegExp {
    enum RE {
        case Choice(r1:RE, r2:RE)
        case Seq(r1:RE, r2:RE)
        case Star(r:RE)
        case Epsilon
        case Letter(l:Char)
        case Phi
    }

    import RE.* 

    def eps(r:RE):Boolean = false // TODO

    def deriv(r:RE, l:Char):RE = r // TODO 

    def wordMatch(w:List[Char], r:RE):Boolean = false // TODO
}