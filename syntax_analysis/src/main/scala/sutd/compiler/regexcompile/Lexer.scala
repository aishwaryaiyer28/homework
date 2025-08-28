package sutd.compiler.regexcompile

import sutd.compiler.regexcompile.RegExp.*
import sutd.compiler.regexcompile.Parsec.*
import sutd.compiler.regexcompile.Functor.*
import sutd.compiler.regexcompile.Applicative.*
import sutd.compiler.regexcompile.Monad.* 


/**
 * regex external syntax
 * 
 * r ::= [c-c] | [cc] | [] | c |  r|r | r* | r? | rr | (r)
 * c ::= a | ... | z | A | ... | Z | 1 | ... | 0
 * **/


object Lexer {

    // Lexer Environments
    case class LEnv(tokens: List[Char], ln: Int, cl: Int)

    val whitespaces = List('\t', '\r', '\n', ' ', '\f')

    given lenvParserEnv:ParserEnv[LEnv, Char] = new ParserEnv[LEnv, Char] {
        override def getTokens(env: LEnv): List[Char] = env match {
            case LEnv(toks, ln, cl) => toks
        }
        override def getCol(env: LEnv): Int = env match {
            case LEnv(toks, ln, cl) => cl
        }
        override def getLine(env: LEnv): Int = env match {
            case LEnv(toks, ln, cl) => ln
        }
        override def setTokens(ts: List[Char])(env: LEnv): LEnv = env match {
            case LEnv(toks, ln, cl) => LEnv(ts, ln, cl)
        }
        override def setLine(l: Int)(env: LEnv): LEnv = env match {
            case LEnv(toks, _, cl) => LEnv(toks, l, cl)
        }

        override def setCol(c: Int)(env: LEnv): LEnv = env match {
            case LEnv(toks, ln, _) => LEnv(toks, ln, c)
        }
    }

    // source location
    case class SrcLoc(line:Int, col:Int)

    // Lexer output tokens

    enum LToken {
        case LBracket(src:SrcLoc) // [
        case RBracket(src:SrcLoc) // ] 
        case Hyphen(src:SrcLoc)   // -
        case VertBar(src:SrcLoc)  // | 
        case Asterix(src:SrcLoc)  // * 
        case Question(src:SrcLoc) // ?
        case LParen(src:SrcLoc)   // (
        case RParen(src:SrcLoc)   // )
        case AlphaNum(src:SrcLoc, char:Char) // a,b,c, ... ,A, B, C, ... 0, ... 9
        case WhiteSpace(src:SrcLoc, char:Char) 
    }
    import LToken.* 

    def srcLoc(tok:LToken):SrcLoc = tok match {
        case LBracket(src)      => src
        case RBracket(src)      => src
        case Hyphen(src)        => src
        case VertBar(src)       => src
        case Asterix(src)       => src
        case Question(src)      => src 
        case LParen(src)        => src
        case RParen(src)        => src
        case AlphaNum(src, c)   => src
        case WhiteSpace(src, c) => src
    }

    def l_sym_lbrack(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '[')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (LBracket(SrcLoc(ln,cl)))

    def l_sym_rbrack(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == ']')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (RBracket(SrcLoc(ln,cl)))

    def l_sym_hyphen(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '-')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (Hyphen(SrcLoc(ln,cl)))

    def l_sym_vertbar(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '|')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (VertBar(SrcLoc(ln,cl)))
    
    def l_sym_asterix(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '*')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (Asterix(SrcLoc(ln,cl)))

    def l_sym_question(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '?')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (Question(SrcLoc(ln,cl)))
    
    def l_sym_lparen(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == '(')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (LParen(SrcLoc(ln,cl)))
    
    def l_sym_rparen(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => c == ')')
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (RParen(SrcLoc(ln,cl)))

    def l_alphanum(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => ('a' to 'z').contains(c) || ('A' to 'Z').contains(c) || ('0' to '9').contains(c))
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (AlphaNum(SrcLoc(ln,cl), c))

    def l_whitespace(using pe:ParserEnv[LEnv, Char]):Parser[LEnv, LToken] = for {
        c <- sat((c:Char) => whitespaces.contains(c))
        ln <- get(lenv => pe.getLine(lenv))
        cl <- get(lenv => pe.getCol(lenv))
    } yield (WhiteSpace(SrcLoc(ln,cl), c))
    

    def lexOne:Parser[LEnv, LToken] = 
        choice(l_sym_lbrack)
            (choice(l_sym_rbrack)
                (choice(l_sym_hyphen)
                    (choice(l_sym_vertbar)
                        (choice(l_sym_asterix)
                            (choice(l_sym_question)
                                (choice(l_sym_lparen)
                                    (choice(l_sym_rparen)
                                        (choice(l_alphanum)(l_whitespace)))))))))
    
    def lex:Parser[LEnv, List[LToken]] = many(lexOne)
}   


