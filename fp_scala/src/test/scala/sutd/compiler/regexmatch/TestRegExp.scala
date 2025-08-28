package sutd.compiler.regexmatch

import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.regexmatch.RegExp.*



class TestRegExp extends funsuite.AnyFunSuite {
    import RE.*

    test("test1") {
        // r = (a.b*)
        val r = Seq(Letter('a'), Star(Letter('b')))
        // eps(r) == false
        assert(!eps(r))
    }

    test("test2") {
        // r = (a*.(b*+c))
        val r = Seq(Star(Letter('a')), Choice(Star(Letter('b')), Letter('c')))
        // eps(r) == true
        assert(eps(r))
    }

    test("test3") {
        // r = (a.b*)
        val r = Seq(Letter('a'), Star(Letter('b')))
        // deriv(r,a) == epsilon.b*
        val expected = Seq(Epsilon, Star(Letter('b')))
        assert(deriv(r,'a') == expected)
    }

    test("test4") {
        // r = (a*.(b*+c))
        val r = Seq(Star(Letter('a')), Choice(Star(Letter('b')), Letter('c')))
        // deriv(r,b) == ((phi.a*).(b*+c))+(epsilon.b* + phi)
        val expected =  Choice(Seq(Seq(Phi,Star(Letter('a'))),Choice(Star(Letter('b')),Letter('c'))),Choice(Seq(Epsilon,Star(Letter('b'))),Phi))
        assert(deriv(r,'b') == expected)
    }

    test("test5") {
        // r = (a+b)*
        // w = aaab
        val r = Star(Choice(Letter('a'), Letter('b')))
        val w = "aaab".toList
        // match(w,r) == true
        assert(wordMatch(w,r))
    }

    test("test6") {
        // r = ((a.a)+b)*.c 
        // w = abaac
        val r = Seq(Star(Choice(Seq(Letter('a'), Letter('a')), Letter('b')))  , Letter('c'))
        val w = "abaac".toList
        // match(w,r) == false
        assert(!wordMatch(w,r))
    }
}