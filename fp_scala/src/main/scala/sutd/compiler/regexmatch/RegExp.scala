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

    def eps(r:RE):Boolean = r match {
        case Phi => false 
        case Epsilon => true 
        case Letter(l) => false 
        case Star(r) =>  true
        case Choice(r1, r2) => eps(r1) || eps(r2)
        case Seq(r1, r2) =>  eps(r1) && eps(r2)
    }

    def deriv(r:RE, l:Char):RE = r match {
        case Phi => Phi
        case Epsilon => Phi
        case Letter(l2) => if (l == l2) then Epsilon else Phi
        case Choice(r1, r2) => Choice(deriv(r1, l), deriv(r2, l))
        case Seq(r1, r2) => if eps(r1) then Choice(Seq(deriv(r1, l) ,r2), deriv(r2, l)) else Seq(deriv(r1, l), r2)
        case Star(r) => Seq(deriv(r, l), Star(r))
    } 

    def wordMatch(w:List[Char], r:RE):Boolean = w match {
        case Nil => eps(r)
        case l::tl => wordMatch(tl, deriv(r,l))
    }
}