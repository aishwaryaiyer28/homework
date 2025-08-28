package sutd.compiler.regexcompile

import sutd.compiler.regexcompile.RegExp.*
import sutd.compiler.regexcompile.Parsec.*
import sutd.compiler.regexcompile.Functor.*
import sutd.compiler.regexcompile.Applicative.*
import sutd.compiler.regexcompile.Monad.*
import sutd.compiler.regexcompile.Lexer.*


/** regex external syntax
  *
  * R ::= [C-C] || [CC] || [] || C || R|R || R* || R? || RR || (R) 
  * C ::= a || ... || z || 1 || ... || 0
  *
  * left recursion elimination
  *
  * step 1. remove left recursion in R 
  * R ::= R|R || R* || R? || RR || (R) || [C-C] || [CC] || [] || C 
  * alpha1 == |R 
  * alpha2 == * 
  * alpha3 == ? 
  * alpha4 == R 
  * beta1 == (R)
  * beta2 == [C-C] 
  * beta3 == [CC] 
  * beta4 == [] 
  * thus we have 
  * R ::= (R)S || [C-C]S || [CC]S || []S || CS 
  * S ::= |RS || *S || ?S || RS || eps 
  * C ::= a || ... || z ||  1 || ... || 0
  *
  * step 2. left factorization
  *
  * R ::= (R)S || CS || [T 
  * T :: = CU || ]S 
  * U ::= -C]S || C]S
  * S ::= |RS || *S || ?S || RS || eps 
  * C ::= a || ... || z || 1 || ... || 0 
  *
  */

object Parser {
    import RegExp.*
    import LToken.*
    import Progress.*
    import Result.*

    case class PEnv(toks: List[LToken])

    given penvParserEnv: ParserEnv[PEnv, LToken] = new ParserEnv[PEnv, LToken] {
        override def getTokens(env: PEnv): List[LToken] = env match {
            case PEnv(toks) => toks
        }
        override def getCol(env: PEnv): Int = env match {
            case PEnv(Nil) => -1
            case PEnv(tok :: toks) =>
                srcLoc(tok) match {
                    case SrcLoc(ln, col) => col
                }
        }
        override def getLine(env: PEnv): Int = env match {
            case PEnv(Nil) => -1
            case PEnv(tok :: toks) =>
                srcLoc(tok) match {
                    case SrcLoc(ln, col) => ln
                }
        }
        override def setTokens(ts: List[LToken])(env: PEnv): PEnv = env match {
            case PEnv(_) => PEnv(ts)
        }

    }

    enum R {
        case ParenR(r: R, s: S)
        case Chara(c: Char, s: S)
        case CClassCommon(t: T)
    }

    enum T {
        case CClass(cb: Char,  u: U)
        case EClass(s: S)
    }

    enum U {
        case CClassRange(ce:Char, s:S)
        case CClassChoice(rest:List[Char], s:S)
    }

    enum S {
        case Bars(r: R, s: S)
        case Stars(s: S)
        case Questions(s: S)
        case Rs(r: R, s: S)
        case NIL
    }

    def p_r: Parser[PEnv, R] =
        choice(p_paren_r)(choice(p_chara)(p_cclasscommon))

    import LToken.*
    import R.*
    import S.*
    import T.*
    import U.*
    // R
    def p_paren_r: Parser[PEnv, R] = for {
        _ <- p_lparen
        r <- p_r
        _ <- p_rparen
        s <- p_s
    } yield (ParenR(r, s))

    def p_chara: Parser[PEnv, R] = for {
        c <- p_alphanum
        s <- p_s
    } yield Chara(c, s)

    def p_cclasscommon: Parser[PEnv, R] = for {
        _ <- p_lbracket
        t <- p_t
    } yield CClassCommon(t)

    // T 
    def p_t: Parser[PEnv, T] =
        choice(p_cclass)(p_eclass)

    def p_cclass: Parser[PEnv, T] = for {
        a1  <- p_alphanum
        u <- p_u
    } yield CClass(a1, u)

    def p_eclass: Parser[PEnv, T] = for {
        _ <- p_rbracket
        s <- p_s
    } yield (EClass(s))

    // U
    def p_u: Parser[PEnv, U] = 
        choice(p_cclass_range)(p_cclass_choice)

    def p_cclass_range: Parser[PEnv, U] = for {
        hyp <- p_hyphen
        a2  <- p_alphanum
        rb  <- p_rbracket
        s <- p_s
    } yield CClassRange(a2, s)

    // Task 4 TODO
    def p_cclass_choice: Parser[PEnv, U] = Parsec.Parser( s => Empty(Failed("TODO"))) // TODO: fixme

    // S 
    // Task 4 TODO
    def p_s: Parser[PEnv, S] = Parsec.Parser( s => Empty(Failed("TODO"))) // TODO: fixme


    def p_nil: Parser[PEnv, S] = empty(NIL)

    // lower level parser which parser a Lexer Token and return the lexer Token or character

    def p_lparen: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case LParen(_) => true
            case _         => false
        }
    )

    def p_rparen: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case RParen(_) => true
            case _         => false
        }
    )

    def p_lbracket: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case LBracket(_) => true
            case _           => false
        }
    )

    def p_rbracket: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case RBracket(_) => true
            case _           => false
        }
    )

    def p_hyphen: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case Hyphen(_) => true
            case _         => false
        }
    )

    def p_alphanum: Parser[PEnv, Char] = for {
        t <- sat((t: LToken) =>
            t match {
                case AlphaNum(_, _) => true
                case _              => false
            }
        )
        c <- someOrFail(t)(lt =>
            lt match {
                case AlphaNum(_, ch) => Some(ch)
                case _               => None
            }
        )(
          "p_alphanum() failed with a token parsed but the token is not alpha numeric."
        )
    } yield (c)

    def p_vertbar: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case VertBar(_) => true
            case _          => false
        }
    )

    def p_asterix: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case Asterix(_) => true
            case _          => false
        }
    )

    def p_question: Parser[PEnv, LToken] = sat((t: LToken) =>
        t match {
            case Question(_) => true
            case _           => false
        }
    )

    def p_skip_whitespaces: Parser[PEnv, List[LToken]] =
        everythingUntil((t: LToken) =>
            t match {
                case WhiteSpace(_, _) => false
                case _                => true
            }
        )

    // converting R to RE

    def rtoRE(r: R): RE = r match {
        case ParenR(r, s) => {
            val re = rtoRE(r)
            val cont = stoCont(s)
            cont(re)
        }
        case Chara(c, s) => {
            val re = RE.Letter(c)
            val cont = stoCont(s)
            cont(re)
        }
        case CClassCommon(t) =>
            t match {
                case CClass(cb, u) => {
                    val cont = utoCont(u)
                    cont(cb)
                }

                case EClass(s) => {
                    val re = RE.Epsilon
                    val cont = stoCont(s)
                    cont(re)
                }
            }
    }

    def utoCont(u: U): Char => RE = {
        cb => {
            u match {
                case CClassRange(ce, s) => {
                    val cs = (cb to ce).toList
                    val re = cs match {
                        case Nil       => RE.Epsilon
                        case (x :: xs) => mkChoice(cs.map(c => RE.Letter(c)))
                    }
                    val cont = stoCont(s)
                    cont(re)
                }
                case CClassChoice(cs, s) => {
                    val re = mkChoice((cb::cs).map(c => RE.Letter(c)))
                    val cont = stoCont(s)
                    cont(re)
                }
            }
        }
    }

    def stoCont(s: S): RE => RE = s match {
        case Bars(r, s) => {
            val rre = rtoRE(r)
            val cont = stoCont(s)
            (lre => cont(RE.Choice(lre, rre)))
        }
        case Stars(s) => {
            val cont = stoCont(s)
            (re => cont(RE.Star(re)))
        }
        case Questions(s) => {
            val cont = stoCont(s)
            (re => cont(RE.Choice(re, RE.Epsilon)))
        }
        case Rs(r, s) => {
            val re2 = rtoRE(r)
            val cont = stoCont(s)
            (re1 => cont(RE.Seq(re1, re2)))
        }
        case NIL => {
            (re => re)
        }
    }

    def parse_regex(toks:List[LToken]):Either[String, RE] = {
        run(p_r)(PEnv(toks)) match {
            case Consumed(Ok(r,e)) => Right(rtoRE(r))
            case Consumed(Failed(msg)) => Left(msg)
            case Empty(Ok(r,e)) => Left("parser consumed nothing.")
            case Empty(Failed(msg)) => Left(msg)
        }
    }

}
