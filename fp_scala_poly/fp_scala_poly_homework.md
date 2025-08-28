% Parametric Polymorphism and Adhoc Polymorphism


# Compiling Regular expression 
In this homework, you are tasked to compile a regular expression into a state machine.


## Syntax (Recap)
Recall from the last homework, we consider the grammar that describes the valid syntax of a regular expression.

$$
\begin{array}{rccl} 
{\tt (RegularExpression)} & r & ::= & r+r \mid r.r \mid r^* \mid \epsilon \mid l \mid \phi \\ 
{\tt (Letter)} & l & ::= & a \mid b \mid ... \\ 
{\tt (Word)} & w & ::= & lw \mid \epsilon
\end{array}
$$

where 

* $r_1+r_2$ denotes a choice of $r_1$ and $r_2$.
* $r_1.r_2$ denotes a sequence of $r_1$ followed by $r_2$.
* $r^*$ denotes a kleene's star, in which $r$ can be repeated 0 or more times.
* $\epsilon$ denotes an empty word, (i.e. empty string)
* $l$ denotes a letter symbol
* $\phi$ denotes an empty regular expression, which matches nothing (not even the empty string).

A word $w$ is a sequence of letter symbols. We write $\epsilon$ to denote an empty word. Note that for all word $w$, we have $w \epsilon = w = \epsilon w$

The syntatic rules of regular expression language can be easily modeled using Algebraic datatype. You may find the given codes in the project stub.

## Derivative (Recap)
And recall that in the last homework, we implemented a simple word matcher for regular expression using the derivative operation.

The derivative a regular expression $r$ with respect to a letter $l$ is a regular expression defined as follows

$$
\begin{array}{rcl}
deriv(\phi, l) & = & \phi \\ \\
deriv(\epsilon, l) & = & \phi \\ \\
deriv(l_1, l_2) & = & \left [ 
    \begin{array}{ll}
    \epsilon & {if\ l_1 = l_2} \\ 
    \phi & {otherwise}
    \end{array}
    \right . \\ \\
deriv(r_1+r_2, l) & = & deriv(r_1, l) + deriv(r_2, l) \\ \\
deriv(r_1.r_2, l) & = & \left [ 
    \begin{array}{ll}
    deriv(r_1,l).r_2 + deriv(r_2,l) & {if\ eps(r_1)} \\
    deriv(r_1,l).r_2 & {otherwise}
    \end{array} \right . \\ \\ 
deriv(r^*, l) & = & deriv(r,l).r^*
\end{array}
$$

Where $eps(r)$ tests whether $r$ possesses the empty word $\epsilon$.

$$
\begin{array}{rcl}
eps(r_1+r_2) & = & eps(r_1)\ \vee eps(r_2) \\
eps(r_1.r_2) & = & eps(r_1)\ \wedge eps(r_2) \\ 
eps(r^*) & = & true \\ 
eps(\epsilon) & = & true \\ 
eps(l) & = & false \\ 
eps(\phi) & = & false 
\end{array}
$$

We can define $match(w,r)$ in terms of $deriv(\_,\_)$. 

$$
match(w,r) = \left [
    \begin{array}{ll}
    eps(r) & {if\ w = \epsilon} \\ 
    match(w', deriv(r,l)) & {if\ w = lw'}
    \end{array} 
    \right .
$$



## Correspondence to State Machine

Recall from one of our freshmore module DDW, that a state machine consists a set of states and a set of transitions. 

We could use the following type class to describe a state machine in Scala.

```scala
trait StateMachine[S,L] {
    def step(state:S, symb:L):Option[S]
    def isFinal(state:S):Boolean
}
```
The type class `StateMachine` has two type arguments, `S` denotes the states, and `L` denotes the symbols (i.e. letters). 
There are two member functions. `step` defines the stepping function which transits from one state to another via a symbol. 
`isFinal` checks whether the given state is final.  


We can define the following function to run a state machine over a list of symbols.

```scala
def runStateMachine[S,L](s:S,symbs:List[L])(using machine:StateMachine[S,L]):Boolean = symbs match {
    case Nil => machine.isFinal(s)
    case (l::ls) => {
        machine.step(s,l) match {
            case None    => false
            case Some(t) => runStateMachine(t, ls)

        }
    }
}
```

It is well known that the set of strings (language) described by a regular expression can be accepted by a state machine. 
There are many existing algorithms that convert a regular expression into an equivalent state machine.

There several reasons why we would need such a conversion. 
1. To estabalish the correspondence between the regular expression and the equivalant  state machine. 
2. To optimize the matching operation, for instance, the `match` function defined using the derivative operation is not too efficient because for each input symbol, we need to use it to navigate through the syntax tree structure of the regular expression (derivative) to compute the next regular expression (derivative). These navigation can be pre-computed and cached in a lookup table.



## Task 1 

In this task, you need to define a type class instance to show that there exists a correspondence between regular expression and the state machine. 

```scala
// task 1.
given derivFSA:StateMachine[RE, Char] = new StateMachine[RE,Char] {
    def step(r:RE, l:Char):Option[RE] = None // TODO: Fix me
    def isFinal(r:RE):Boolean = false // TODO: Fix me
}
```

### Hint: 
Out of the three functions defined for regular expression derivative matching in the last homework, which two can be used to implement `step` and `isFinal`?

### Test cases
Here are some test cases you may find in the project stub.

```scala
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
```

## Task 2 


In this task and the next task, we are going to implement a conversion algorithm which produces a more efficient state machine.

As we mentioned earlier, the idea is to pre-compute (compile) all the possible transitions of the given regular expression before the actual execution (with the input words). In order to do that, we have to ensure that there finitely many transitions. Assuming the set of symbols is finite, having a set of finite states implies that the set of transitions is also finite. 

From the previous tasks, we know that the symbols of the state machine must be the same the letters in the regular expression, the regular expression (derivatives) are mostly likely the states in the state machine we are looking for. The question is "is the set of regular expression derivatives finite?"

Let's consider the following example. 

$$
\begin{array}{ll}
deriv(a^*.a^*, a) & = \\
deriv(a^*,a).a^* + deriv(a^*,a) & = \\ 
deriv(a,a).a^*.a^* + deriv(a, a).a^* & = \\ 
\epsilon.a^*.a^* + \epsilon.a^*  
\end{array}
$$

And if we apply derivative operation to the above result

$$
\begin{array}{ll}
deriv(\epsilon.a^*.a^* + \epsilon.a^*, a) & = \\
deriv(\epsilon.a^*.a^*, a) + deriv(\epsilon.a^*, a) & = \\
deriv(\epsilon, a).a^*.a^* + deriv(a^*.a^*, a) + deriv(\epsilon, a).a^* + deriv(a^*, a) & =  \\ \phi.a^*.a^* + \epsilon.a^*.a^* + \epsilon.a^*  +  + \phi.a^* + \epsilon.a^*
\end{array}
$$

As we can observe that the structure of the regular expression increases as we apply derivative operation. 
If we were to continue to repeat the process, we will encounter infinitely many regular expression derivatives.

As pointed out by Brzozoswki, the set of derivative descendants of a regular expression can be finite if we apply some simplification.

We note that the following equations among regular expressions hold.

$$
\begin{array}{rcl}
\epsilon.r & = & r \\
\phi.r & = & \phi \\
r + r & = & r \\ 
(r_1 + r_2) + r_3 & = & r_1 + (r_2 + r_3) \\ 
(r_1 . r_2) . r_3 & = & r_1. (r_2. r_3) \\  
r_1 + r_2 & = & r_2 + r_1 
\end{array}
$$

For simplification purpose, we can apply the first three equiations in the direction of left to right to shrink the size of regular expressions. (We could have included more, e.g. $r.\epsilon = r$. However as noted by some earlier work, these three rules are sufficient. )

For the last three equations, we can't apply them directly to reduce the size of the regular expressions. However, we make use of them to "normalize" the regular expression nested structure so that, it is easier for us to apply the first three simplification rules.


### Task 2.1 - Testing of Epsilon and Phi

To apply the first two simplification rules, we can take advantage of the leading $\epsilon$ and $\phi$. However not all the regular expression would have this pattern trivially. We need some extra rules to identify $\epsilon$ and $\phi$ sub-expressions. 

We consider the following functions $isEps(r)$ tests whether the given $r \equiv \epsilon$, i.e. ${\cal L}(r) = {\cal L}(\epsilon)$, and $isPhi(r)$ test whether the given $r \equiv \phi$. (Note: `isEps` and `eps` are two different functions.)

$$
\begin{array}{rcl}
isEps(\epsilon) & = & true \\ 
isEps(r_1 + r_2) & = & isEps(r_1) \wedge isEps(r_2) \\
isEps(r_1.r_2) & = & isEps(r_1) \wedge isEps(r_2) \\
isEps(r^*) & = & isEps(r) \vee isPhi(r) \\ 
isEps(l) & = & false \\ 
isEps(\phi) & = & false \\ \\ 
isPhi(\epsilon) & = & false \\ 
isPhi(r_1 + r_2) & = & isPhi(r_1) \wedge isPhi(r_2) \\
isPhi(r_1. r_2) & = & isPhi(r_1) \vee  isPhi(r_2) \\
isPhi(r^*) & = & false \\ 
isPhi(l) & = & false \\ 
isPhi(\phi) & = & true 
\end{array}
$$


Your task is to implement the $isEps$ and $isPhi$ functions in Scala.

### Test Cases

```scala
test("is_eps_1") {
        // r = (aa)*
        val r = Star(Seq(Letter('a'), Letter('a')))
        assert(isEps(r) == false)
    }

test("is_eps_2") {
    // r = (eps.(eps+eps))*
    val r = Star(Seq(Epsilon, Choice(Epsilon, Epsilon)))
    assert(isEps(r) == true)
}

test("is_phi_1") {
    // r = (eps.(eps+eps))*
    val r = Star(Seq(Epsilon, Choice(Epsilon, Epsilon)))
    assert(isPhi(r) == false)
}

test("is_phi_2") {
    // r = eps.(phi+phi)
    val r = Seq(Epsilon, Choice(Phi, Phi))
    assert(isPhi(r) == true)
}
```


### Task 2.2 - Normalizing Choice

In this task, we would like to exploit the 3rd, the 4th and the last simplifcation equations we mentioned earlier to normalize and simplify choice regular expression. 

Let's reconsider the last simplifcation rule.

$$
r_1 + r_2 = r_2 + r_1
$$

we could apply this equation from left to right or right to left. However, to avoid non-termination, we should fix one. To do so, it might better to impose a specific order among regular expression. Let's say on the top level

$$
 \phi < \epsilon < l  < r_1+r_2 < r_3.r_4 < r_5*
$$

The ordering between two letters, can be determined by their alphabetic or ascii ordering, e.g. $a < b$.

For choice, sequence and kleene's star, we compare the sub-expressions when two regular expressions are equal at the top level.

$$
\begin{array}{rc}
{\tt (OChoice1)} & 
               \begin{array}{c} 
               r_1 < r_3   \\
               \hline
               r_1 + r_2 < r_3 + r_4   
               \end{array} \\ \\
{\tt (OChoice2)} & 
               \begin{array}{c} 
               r_2 < r_4   \\
               \hline
               r + r_2 < r + r_4   
               \end{array} \\ \\ 
{\tt (OSeq1)} & 
               \begin{array}{c} 
               r_1 < r_3   \\
               \hline
               r_1. r_2 < r_3 . r_4   
               \end{array} \\ \\ 
{\tt (OSeq2)} & 
               \begin{array}{c} 
               r_2 < r_4   \\
               \hline
               r . r_2 < r . r_4   
               \end{array} \\ \\  
{\tt (OStar)} & 
               \begin{array}{c} 
               r_1 < r_2   \\
               \hline
               r_1^* < r_2^*   
               \end{array} 
\end{array}
$$

Complete the type class instance definition of `reOrdering` given in the project stub. (Recall that `Ordering[A]` is a predefined type class in Scala.)


### Test cases

You may find test cases in the given project stub.

```scala
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
```



## Task 2.3 - Removing duplicate choice alternatives

Given that the order among regular expression is fixed, we can normalize choice regular expression

```scala
def norm(r:RE):RE = {
        val rs = normChoice(r)
        mkChoice(rs)
    }

def normChoice(r:RE):List[RE] = r match {
    case Choice(r1,r2) => {
        val nr2 = normChoice(r2)
        val nr1 = normChoice(r1)
        rmdup((nr1 ++ nr2).sortBy(r => r))
    }
    case _ => List(normSeq(r))
}

def rmdup(rs:List[RE]):List[RE] = rs // TODO: fixme

def mkChoice(rs:List[RE]):RE = rs match {
    case Nil => Phi
    case List(r) => r
    case (r::rs1) => Choice(r, mkChoice(rs1))
}

def normSeq(r:RE):RE = r match {
    case Seq(r1,r2) => r1 match {
        case Seq(r11,r12) => normSeq(Seq(r11, Seq(r12, r2)))
        case _ => Seq(r1, normSeq(r2))
    }
    case _ => r 
}
```

The `norm` function normalizes a regular expression `r` by applying `normChoice`. 
`normChoice` sorts alternatives from a choice regular expression and put them in a list. e.g. `normChoice(Choice(Letter('c'), Choice(Letter('a'), Letter('c'))))` yields `List(Letter('a'), Letter('c'), Letter('c'))`. `mkChoice` turns list of regular expression alternatives back to a choice regular expression, e.g. `Choice(Letter('a'), Choice(Letter('c'), Letter('c'))`. `normSeq` normalizes a sequence regular expression according to the 5th simplification equation. 

Note that `rmdup` function is left unfinished, which is supposed to take a list of sorted regular expression alternatives, and to remove the duplication, e.g. `List(Letter('a'), Letter('c'), Letter('c'))` should become `List(Letter('a'), Letter('c'))`.

Your task is the complete the `rmdup` function. 

### Test cases


```scala
test("test_norm_1") {
    // r = (((a.b).c) + a*) + (a.(b.c))
    val r = Choice(Choice(Seq(Seq(Letter('a'),Letter('b')),Letter('c')), Star(Letter('a'))), Seq(Letter('a'), Seq(Letter('b'), Letter('c'))))
    // norm(r) = (a.(b.c))+a*
    val expected = Choice(Seq(Letter('a'),Seq(Letter('b'),Letter('c'))),Star(Letter('a')))
    assert(norm(r) == expected)
}
```

## Task 2.4 - Simplification

With all the helper functions in place, we are going to implement the simplification function.

```scala
def simp1(r:RE):RE = r match {
    case Choice(r1,r2) if (isPhi(r1) && isPhi(r2)) => Phi
    case Choice(r1,r2) if (isPhi(r1)) => simp1(r2)
    case Choice(r1,r2) if (isPhi(r2)) => simp1(r1)
    case Choice(r1,r2) => norm(Choice(simp1(r1), simp1(r2)))
    case Seq(r1,r2)    => Seq(r1,r2) // TODO: fixme
    case Star(r1)      => Star(r1) // TODO: fixme
    case _             => r
}

def simp(r:RE):RE = {
    val r1 = simp1(r)
    if (r1 == r) { r1 } else simp(r1)
}

```

Function `simp1` apply simplification rules (the 6 equations) by making use of `isPhi`, `isEps`, `norm` functions. Function `simp` keeps applying `simp1` to the given regular expression until there is no more simplification rules applicable. 

Your task is to complete the unfinished `simp1` function.

### Test cases

```scala
test("test_simp_1") {
    // r = b*
    val r = Star(Letter('b'))
    // deriv(deriv(deriv(r,b),b),b)
    val drbbb = deriv(deriv(deriv(r,'b'),'b'), 'b')
    assert(simp(drbbb) == Star(Letter('b')))
}


test("test_simp_2") {
    // r = (bb)*
    val r = Star(Seq(Letter('b'),Letter('b')))
    // deriv(r,b)
    val drb = deriv(r,'b')
    assert(simp(drb) == Seq(Letter('b'),Star(Seq(Letter('b'),Letter('b')))))
}

```

### Task 2.5 - compiling 


With the simplication function, we next look at the regular-expression-to-state-machine compilation. 

Firstly we need to define a `sigma` function which extracts all the letters from the given regular expression.

```scala
def sigma(r:RE):Set[Char] = r match {
    case Choice(r1, r2) => sigma(r1).union(sigma(r2))
    case Seq(r1, r2)    => sigma(r1).union(sigma(r2))
    case Star(r1)       => sigma(r1)
    case Letter(l)      => Set(l)
    case Epsilon        => Set()
    case Phi            => Set()
}
```

Secondly, we define a `build` function which applies derivative and simplication to extract all the possible transitions.

```scala
def build(r:RE, sig:Set[Char]):List[(RE, Char, RE)] = {
    def go(newDs:Set[RE], seenDs:Set[RE], delta:List[(RE,Char,RE)]):List[(RE,Char,RE)] = newDs.toList match {
        case Nil => delta
        case _::_ => { 
            val newDelta = newDs.toList.flatMap ( r => {
                sig.toList.map( l => (r, l, simp(deriv(r,l))))
            })
            val nextNewDs = newDelta.map( (x:(RE,Char,RE)) => x match { 
                case (r,l,d) => d
            }).filter( r => !seenDs.contains(r)).toSet
            val nextSeenDs = seenDs.union(newDs)
            go(nextNewDs, nextSeenDs, delta ++ newDelta)
        }
    }
    go(Set(r), Set(), List())
}

```


Finally, we define a `compile` function which leverages the `sigma` and the `build` functions to compile a regular expression into a state machine, where states are collected from all the derivatives and mapped to unique integers. Transitions are stored in a `Map[(Int, Char), Int]` look-up table, whose key is `(Int, Char)`, namely, the source state and symbol,  and the value is `Int`, i.e. the target stae. A `Map[K,V]` object in Scala is similar to a python dictionary, where `K` is the key type. and `V` is the value type. Given `Map[K,V]` object `m` and a key `k`, `m.get(k)` returns an `Option[V]` result. When the key is present, `Some(v)` will be returned, otherwise `None`.
> Fore more details in how to use Map data type in Scala, please refer to <https://docs.scala-lang.org/scala3/book/collections-classes.html#maps>

```scala
def compile(r:RE):StateMachine[Int, Char] = { 
    val allSymbs  = sigma(r)
    val delta     = build(r, allSymbs) // assumption, the first item in the list should contain the init state as the first item
    val allStates:List[RE] = List()                    // TODO: fixme. Extract all the source states from delta.
    val allStatesExceptR   = allStates.filter( x => x != r )
    val table:Map[RE,Int]  = allStatesExceptR.foldLeft(Map(r -> 0))( (acc,s) => if (!acc.contains(s)) { acc + (s -> (acc.values.max + 1) )} else { acc })
    val delta_numeric:List[(Int, Char, Int)] = List() // TODO: fixme. convert the states found in delta from RE to Int.
    val delta_numeric_map:Map[(Int, Char), Int] = delta_numeric.foldLeft(Map():Map[(Int, Char), Int])((acc, t:(Int, Char, Int)) => t match { case (rn, l, dn) => acc + ((rn, l) -> dn)})
    val final_numeric = table.toList.flatMap( p => p match { 
        case (r, i) if eps(r) => List(i)
        case (r, i)           => Nil
    }).toSet

    new StateMachine[Int, Char] {
        def step(s:Int, l:Char):Option[Int] = delta_numeric_map.get((s,l)) 
        def isFinal(state: Int): Boolean = final_numeric.contains(state)
    }
}
```

Complete the missing parts in the above `compile` function. 

### Test cases

```scala
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
```