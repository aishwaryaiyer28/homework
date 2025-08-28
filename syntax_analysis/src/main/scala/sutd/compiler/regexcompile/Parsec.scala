package sutd.compiler.regexcompile

import sutd.compiler.regexcompile.Functor.*
import sutd.compiler.regexcompile.Applicative.*
import sutd.compiler.regexcompile.Monad.*

object Parsec {
    enum Progress[+A] {
        case Consumed(value: A)
        case Empty(value: A)
    }
    type Error = String
    enum Result[+A] {
        case Ok(value: A)
        case Failed(msg: Error)
    }
    trait ParserEnv[E, T] {
        def getTokens(env: E): List[T]
        def getLine(env: E): Int = 0 // default
        def getCol(env: E): Int = 0 // default
        def setTokens(ts: List[T])(env: E): E
        def setLine(l: Int)(env: E): E = env // default
        def setCol(c: Int)(env: E): E = env // default
    }


    import Progress.*
    import Result.*
    case class Parser[E, A](p: E => Progress[Result[(A, E)]]) {
        def map[B](f: A => B): Parser[E, B] = this match {
            case Parser(ea) =>
                Parser(env =>
                    ea(env) match {
                        case Empty(Failed(err))    => Empty(Failed(err))
                        case Empty(Ok((a, env1)))  => Empty(Ok((f(a), env1)))
                        case Consumed(Failed(err)) => Consumed(Failed(err))
                        case Consumed(Ok((a, env1))) =>
                            Consumed(Ok((f(a), env1)))
                    }
                )
        }
        def flatMap[B](f: A => Parser[E, B]): Parser[E, B] = this match {
            case Parser(ea) =>
                Parser(env =>
                    ea(env) match {
                        case Consumed(v) => {
                            lazy val cont = v match {
                                case Failed(err) => Failed(err)
                                case Ok((a, env1)) =>
                                    f(a) match {
                                        case Parser(eb) =>
                                            eb(env1) match {
                                                case Consumed(x) => x
                                                case Empty(x)    => x
                                            }
                                    }
                            }
                            Consumed(cont)
                        }
                        case Empty(v) =>
                            v match {
                                case Failed(err) => Empty(Failed(err))
                                case Ok((a, env1)) =>
                                    f(a) match {
                                        case Parser(eb) => eb(env1)
                                    }
                            }
                    }
                )
        }
    }

    def run[E, A](
        parser: Parser[E, A]
    )(env: E): Progress[Result[(A, E)]] = parser match {
        case Parser(p) => p(env)
    }

    type ParserM = [E] =>> [A] =>> Parser[E, A]

    given parsecMonadError[E]: MonadError[ParserM[E], Error] =
        new MonadError[ParserM[E], Error] {
            override def pure[A](a: A): Parser[E, A] =
                Parser(cs => Empty(Ok((a, cs))))
            override def bind[A, B](
                fa: Parser[E, A]
            )(f: A => Parser[E, B]): Parser[E, B] = fa.flatMap(f)
            override def raiseError[A](e: Error): Parser[E, A] =
                Parser(env => Empty(Failed(e)))
            override def handleErrorWith[A](
                fa: Parser[E, A]
            )(f: Error => Parser[E, A]): Parser[E, A] = fa match {
                case Parser(ea) =>
                    Parser(env =>
                        ea(env) match {
                            case Empty(
                                  Failed(err)
                                ) => // only backtrack when it is empty
                                {
                                    f(err) match {
                                        case Parser(ea2) => ea2(env)
                                    }
                                }
                            case Empty(
                                  Ok(v)
                                ) => // LL(1) parser will also attempt to look at f if fa does not consume anything
                                {
                                    f("faked error") match {
                                        case Parser(ea2) =>
                                            ea2(env) match {
                                                case Empty(_) =>
                                                    Empty(
                                                      Ok(v)
                                                    ) // if f also fail, we report the error from fa
                                                case consumed => consumed
                                            }
                                    }
                                }
                            case Consumed(v) => Consumed(v)
                        }
                    )
            }

        }

    // some combinators
    // alternative, w/o backtracking once committed
    def choice[E, A](p: Parser[E, A])(q: Parser[E, A])(using
        m: MonadError[ParserM[E], Error]
    ): Parser[E, A] = m.handleErrorWith(p)(e => q)

    def get[E, A](op: E => A): Parser[E, A] =
        Parser(env => Empty(Ok((op(env), env))))

    def tokens[T, E](env: E)(using pe: ParserEnv[E, T]): List[T] =
        pe.getTokens(env)

    def line[T, E](env: E)(using pe: ParserEnv[E, T]): Int = pe.getLine(env)

    def col[T, E](env: E)(using pe: ParserEnv[E, T]): Int = pe.getCol(env)

    def getTokens[E, A, T](using pe:ParserEnv[E, T]):Parser[E, List[T]] = get(tokens)

    def getLine[E, A, T](using pe:ParserEnv[E,T]):Parser[E, Int] = get(line)

    def getCol[E, A, T](using pe:ParserEnv[E,T]):Parser[E, Int] = get(col)

    def set[E, T](op: E => E): Parser[E, Unit] =
        Parser(env => Empty(Ok(((), op(env)))))


    // TODO: instead of println, we should put it into a writer monad
    def log[E, T](mesg:String):Parser[E, Unit] = 
        Parser(env => {
            println(mesg)
            Empty(Ok((),env))
        })

    // unconditionally parse a single item
    def item[E, T](using pe: ParserEnv[E, T]): Parser[E, T] =
        Parser((env: E) => {
            val toks = pe.getTokens(env)
            val ln = pe.getLine(env)
            val col = pe.getCol(env)
            toks match {
                case Nil =>
                    Empty(
                      Failed(
                        s"item() is called with an empty token stream"
                      )
                    )
                case (c :: cs) if c == '\n' =>
                    Consumed(Ok((c, pe.setCol(1)(pe.setLine(ln + 1)(pe.setTokens(cs)(env))))))
                case (c :: cs) =>
                    Consumed(Ok((c, pe.setCol(col + 1)(pe.setTokens(cs)(env)))))
            }
        })

    def sat[E, T](p: T => Boolean)(using pe: ParserEnv[E, T]): Parser[E, T] = Parser(
      (env: E) => {
          val toks = pe.getTokens(env)
          val ln = pe.getLine(env)
          val col = pe.getCol(env)
          toks match {
              case Nil =>
                  Empty(
                    Failed(
                      s"sat() is called with an empty token stream at line ${ln}, col ${col}"
                    )
                  )
              case (c :: cs) if p(c) && c == '\n' =>
                  Consumed(Ok((c, pe.setCol(1)(pe.setLine(ln + 1)(pe.setTokens(cs)(env))))))
              case (c :: cs) if p(c) =>
                  Consumed(Ok((c, pe.setCol(col + 1)(pe.setTokens(cs)(env)))))
              case (c :: cs) =>
                  Empty(
                    Failed(
                      s"sat() is called with a unsatisfied predicate with token ${c} at line ${ln}, col ${col}"
                    )
                  )

          }
      }
    )

    // explicit try and backtrack if fails
    def attempt[E, A](p: Parser[E, A]): Parser[E, A] =
        Parser(env =>
            run(p)(env) match {
                case Consumed(Failed(err)) => Empty(Failed(err))
                case otherwise =>
                    otherwise // undo the consumed effect if it fails
            }
        )

    // one or more
    def many1[E, A, T](p: Parser[E, A])(using pe:ParserEnv[E,T]): Parser[E, List[A]] = for {
        a <- p
        as <- many(p)
    } yield (a :: as)

    // zero or more
    def many[E, A, T](p: Parser[E, A])(using pe:ParserEnv[E,T]): Parser[E, List[A]] = {
        Parser(env =>
            run(manyOp(p))(env) match {
                case Empty(Ok((x, env1))) => Empty(Ok((x.reverse, env1)))
                case Empty(Failed(err))   => Empty(Failed(err))
                case Consumed(Ok((x, env1))) =>
                    Consumed(Ok((x.reverse, env1)))
                case Consumed(Failed(err)) => Consumed(Failed(err))
            }
        )
    }

    def manyOp[E, A, T](p: Parser[E, A])(using pe:ParserEnv[E,T]): Parser[E, List[A]] = {
        def walk(acc: List[A])(
            env: E
        )(r: Progress[Result[(A, E)]]): Result[(List[A], E)] =
            r match {
                case Empty(Failed(err)) => Ok((acc, env))
                case Empty(Ok(v)) =>
                    Failed(
                      s"manyOp() is applied which yields a possible empty value but nothing is consumed at line ${pe.getLine(env)} col ${pe.getCol(env)}."
                    ) // not making progress
                case Consumed(Failed(err)) => Failed(err)
                case Consumed(Ok((x, env1))) =>
                    val acc_ = (x :: acc)
                    walk(acc_)(env1)(run(p)(env1))
            }
        Parser(env =>
            run(p)(env) match {
                case Empty(Failed(err)) => Empty(Ok((Nil, env)))
                case Empty(Ok(v)) =>
                    Empty(
                      Failed(
                        s"manyOp() is applied a sub parser which yields a possible empty value and nothing is consumed at line ${pe.getLine(env)} col ${pe.getCol(env)}."
                      )
                    )
                case Consumed(x) => Consumed(walk(Nil)(env)(Consumed(x)))
            }
        )
    }

    // interleave As with B as delimeter
    def interleave[T, A, B](
        pa: Parser[T, A]
    )(pb: Parser[T, B]): Parser[T, List[A]] = {
        lazy val p1 = for {
            a <- pa
            b <- pb
            as <- interleave(pa)(pb)
        } yield (a :: as)
        lazy val p2 = for {
            a <- pa
        } yield (List(a))
        choice(attempt(p1))(p2) // for comprehesion is not composable			?
    }

    // either one
    // backtrack even when committed
    def either1[A, B, T](
        pa: Parser[T, A]
    )(pb: Parser[T, B]): Parser[T, Either[A, B]] = {
        val p1: Parser[T, Either[A, B]] = for (a <- pa) yield Left(a)
        lazy val p2: Parser[T, Either[A, B]] = for (b <- pb) yield Right(b)
        choice(attempt(p1))(p2)
    }

    // optional
    def optional[T, A](pa: Parser[T, A]): Parser[T, Either[A, Unit]] = {
        val p1: Parser[T, Either[A, Unit]] = for (a <- pa) yield (Left(a))
        lazy val p2: Parser[T, Either[A, Unit]] =
            Parser(env => Empty(Ok((Right(()), env))))
        choice(attempt(p1))(p2)
    }

    // everything until condition
    def everythingUntil[E, T](p: T => Boolean)(using pe:ParserEnv[E,T]): Parser[E, List[T]] = {
        // need to create some local function to get around the local type inference
        def rest(t: T): Parser[E, List[T]] =
            if (!p(t)) { for { c <- item;  cs <- everythingUntil(p) } yield (c :: cs) }
            else { Parser(env => Empty(Ok((Nil, env)))) }
        for {
            // t <- item // a bug here? yes, t is consumed, even p(t) is true and return Ok(Nil) but t is already consumed.
            t <- lookAhead(item)
            r <- rest(t)
        } yield r
    }

    // get something without consuming the input
    def lookAhead[E, A](p: Parser[E, A]): Parser[E, A] = {
        // need to create some local function to get around the local type inference
        def getEnv: Parser[E, E] = get(identity)
        def setEnv(e: E): Parser[E, Unit] = set((x:E) => e)
        for {
            env <- getEnv
            x <- p
            () <- setEnv(env)
        } yield x
    }

    // apply f to a to extract b, if the result is None, signal failure
    def someOrFail[E, A, B](a:A)( f:A=>Option[B])(err:Error):Parser[E, B] = Parser(
        env => f(a) match {
            case Some(v) => Empty(Ok((v, env)))
            case None => Empty(Failed(err))
        }
    )
    // not consuming anything and return the given value.
    def empty[E, A](a:A):Parser[E,A] = Parser( env => Empty(Ok((a, env))))

}
