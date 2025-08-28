package sutd.compiler.regexcompile

import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.regexcompile.RegExp.*
import sutd.compiler.regexcompile.Parsec.*
import sutd.compiler.regexcompile.Lexer.*
import sutd.compiler.regexcompile.Parser.*



class TestParser extends funsuite.AnyFunSuite {
    import R.*
    import S.*
    import T.* 
    import U.*
    import LToken.*
    import Progress.*
    import Result.*
    import RE.*
    
    test("test parsing 1") {
        // s = [a-z]*
        val  toks:List[LToken] = List(LBracket(SrcLoc(0,1)), AlphaNum(SrcLoc(0,2),'a'), Hyphen(SrcLoc(0,3)), AlphaNum(SrcLoc(0,4),'z'), RBracket(SrcLoc(0,5)), Asterix(SrcLoc(0,6)))

        val expected = Star(Choice(Letter('a'),Choice(Letter('b'),Choice(Letter('c'),Choice(Letter('d'),Choice(Letter('e'),Choice(Letter('f'),Choice(Letter('g'),Choice(Letter('h'),Choice(Letter('i'),Choice(Letter('j'),Choice(Letter('k'),Choice(Letter('l'),Choice(Letter('m'),Choice(Letter('n'),Choice(Letter('o'),Choice(Letter('p'),Choice(Letter('q'),Choice(Letter('r'),Choice(Letter('s'),Choice(Letter('t'),Choice(Letter('u'),Choice(Letter('v'),Choice(Letter('w'),Choice(Letter('x'),Choice(Letter('y'),Letter('z')))))))))))))))))))))))))))

        parse_regex(toks) match {
            case Left(err) => assert(false)
            case Right(r) => assert( r == expected)
        }
    }
    
    test("test parsing 2") {
        // s = [ab][AC]*
        val  toks:List[LToken] = List(LBracket(SrcLoc(0,1)), AlphaNum(SrcLoc(0,2),'a'), AlphaNum(SrcLoc(0,3),'b'), RBracket(SrcLoc(0,4)), LBracket(SrcLoc(0,5)), AlphaNum(SrcLoc(0,6),'A'), AlphaNum(SrcLoc(0,7),'C'), RBracket(SrcLoc(0,8)), Asterix(SrcLoc(0,9))) 


        val expected = Seq(Choice(Letter('a'),Letter('b')),Star(Choice(Letter('A'),Letter('C')))) 
        parse_regex(toks) match {
            case Left(err) => assert(false)
            case Right(r) => assert( r == expected)
        }
    }
    


    test("test parsing 3") {
        // s = ((ab)|(a))((baa)|a)((ac)|c)
        val  toks:List[LToken] = List(LParen(SrcLoc(0,1)), LParen(SrcLoc(0,2)), AlphaNum(SrcLoc(0,3),'a'), AlphaNum(SrcLoc(0,4),'b'), RParen(SrcLoc(0,5)), VertBar(SrcLoc(0,6)), 
            LParen(SrcLoc(0,7)), AlphaNum(SrcLoc(0,8),'a'), RParen(SrcLoc(0,9)), RParen(SrcLoc(0,10)), LParen(SrcLoc(0,11)), LParen(SrcLoc(0,12)), 
            AlphaNum(SrcLoc(0,13),'b'), AlphaNum(SrcLoc(0,14),'a'), AlphaNum(SrcLoc(0,15),'a'), RParen(SrcLoc(0,16)), VertBar(SrcLoc(0,17)), AlphaNum(SrcLoc(0,18),'a'), 
            RParen(SrcLoc(0,19)), LParen(SrcLoc(0,20)), LParen(SrcLoc(0,21)), AlphaNum(SrcLoc(0,22),'a'), AlphaNum(SrcLoc(0,23),'c'), RParen(SrcLoc(0,24)), 
            VertBar(SrcLoc(0,25)), AlphaNum(SrcLoc(0,26),'c'), RParen(SrcLoc(0,27)))

        val expected = Seq(Choice(Seq(Letter('a'),Letter('b')),Letter('a')),Seq(Choice(Seq(Letter('b'),Seq(Letter('a'),Letter('a'))),Letter('a')),Choice(Seq(Letter('a'),Letter('c')),Letter('c'))))
        parse_regex(toks) match {
            case Left(err) => assert(false)
            case Right(r) => assert( r == expected)
        }
    }


    
}