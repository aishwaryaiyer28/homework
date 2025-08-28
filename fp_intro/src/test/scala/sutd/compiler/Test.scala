package sutd.compiler.helloworld

import scala.language.adhocExtensions
import org.scalatest.funsuite 
import org.scalatest.matchers
import sutd.compiler.helloworld.Main.*

class TestMain extends funsuite.AnyFunSuite {

    test("test1") {
        val expected = 2
        assert(plus_one(1) == expected)
    }
}