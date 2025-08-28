package sutd.compiler.regexcompile

import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.regexcompile.RegExp.*
import sutd.compiler.regexcompile.Automata.*



class TestRegExp extends funsuite.AnyFunSuite {
    import RE.*
    
    test("test_deriv") {
        // r = b*
        val r = Star(Letter('b'))
        // deriv(deriv(deriv(r,b),b),b)        
        val drbbb = deriv(deriv(deriv(r,'b'),'b'), 'b')
        assert(drbbb == Choice(Seq(Phi,Star(Letter('b'))),Choice(Seq(Phi,Star(Letter('b'))),Seq(Epsilon,Star(Letter('b'))))))
    }


    test("test_dr_sm_1") {
        // r = b*
        val r = Star(Letter('b'))
        val w = "bbb".toList
        assert(runStateMachine(r, w))
    }


    test("test_dr_sm_2") {
        // r = (aa)*
        val r = Star(Seq(Letter('a'), Letter('a')))
        val w = "aaa".toList
        assert(!runStateMachine(r, w))
    }

    test("test_dr_sm_3") {
        // r = (aa)*
        val r = Star(Seq(Letter('a'), Letter('a')))
        val w = "aaaa".toList
        assert(runStateMachine(r, w))
    }

    test("test_order_1") {
        // r1 = b*
        val r1 = Star(Letter('b'))
        // r2 = a*
        val r2 = Star(Letter('a'))
        // r2 < r1 
        def cmp(r1:RE, r2:RE)(using reOrdering:Ordering[RE]):Int = {
            reOrdering.compare(r1,r2)
        }
        assert(cmp(r1,r2) > 0)
    }

    test("test_order_2") {
        // r1 = (b+a)*
        val r1 = Star(Choice(Letter('b'), Letter('a')))
        // r2 = (a.b)*
        val r2 = Star(Seq(Letter('a'), Letter('b')))
        // r1 < r2 
        def cmp(r1:RE, r2:RE)(using reOrdering:Ordering[RE]):Int = {
            reOrdering.compare(r1,r2)
        }
        assert(cmp(r1,r2) < 0)
    }


    test("test_norm_1") {
        // r = (((a.b).c) + a*) + (a.(b.c))
        val r = Choice(Choice(Seq(Seq(Letter('a'),Letter('b')),Letter('c')), Star(Letter('a'))), Seq(Letter('a'), Seq(Letter('b'), Letter('c'))))
        // norm(r) = (a.(b.c))+a*
        val expected = Choice(Seq(Letter('a'),Seq(Letter('b'),Letter('c'))),Star(Letter('a')))
        assert(norm(r) == expected)
    }

    test("test_simp_1") {
        // r = b*
        val r = Star(Letter('b'))
        // deriv(deriv(deriv(r,b),b),b)
        val drbbb = deriv(deriv(deriv(r,'b'),'b'), 'b')
        assert(simp(drbbb) == Star(Letter('b')))
    }


    test("test_simp_2") {
        // r = b*
        val r = Star(Seq(Letter('b'),Letter('b')))
        // deriv(r,b)
        val drb = deriv(r,'b')
        assert(simp(drb) == Seq(Letter('b'),Star(Seq(Letter('b'),Letter('b')))))
    }


    


    test("test_dig_sm_1") {
        // r = b*
        val r = Star(Letter('b'))
        given sm:StateMachine[Int,Char] = compile(r)
        val w = "bbb".toList
        assert(runStateMachine(0, w))
    }



    test("test_dig_sm_2") {
        // r = (aa)*
        val r = Star(Seq(Letter('a'), Letter('a')))
        val w = "a".toList
        given sm:StateMachine[Int,Char] = compile(r)
        assert(!runStateMachine(0, w))
    }

    test("test_dig_sm_3") {
        // r = (aa)*
        val r = Star(Seq(Letter('a'), Letter('a')))
        val w = "aa".toList
        given sm:StateMachine[Int,Char] = compile(r)
        assert(runStateMachine(0, w))
    }



}
