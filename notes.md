https://xavierleroy.org/publi/validated-parser.pdf


Definition Predicts extended extending :=
  forall matched, MatchFrontAlign extending matched
    -> MatchFrontAlign extended matched.
Definition Prevents discriminant discriminated :=
  forall matched, MatchFrontAlign discriminant matched
    -> ~(MatchFrontAlign discriminated matched).




there are three cases for a main/against:
1. they are exactly equivalent: EqTotalAlign against main
2. against extends main: EqExtends against main (lookahead = main)
3. main extends against: EqExtends main against (EqDivergesAt lookahead against)
4. they have a point of divergence: (EqDivergesAt lookahead against)

the definition of DivergesAt makes 3 and 4 equivalent, but they have different consequences regarding prediction
in 4, if lookahead (and therefore main) matches, then by construction against can't match since the tail of against doesn't align
but in 3, it instead means that main (and lookahead!) is itself a lookahead for against

or perhaps this is our situation for an inferred unless!!!
in situation 3, merely testing for *main* to match could erroneously cause us to move forward and parse a shorter sequence when the longer sequence could match, so rather than emitting a mere lookahead for main, we emit a *negative* lookahead for against (and a minimal lookahead to test if we should enter main)




main: A
against: B
lookahead: A
lookahead = (firstn 1 main)
EqDivergesAt :=
  TotalAlign (firstn 0 against) (firstn 0 lookahead)
  /\ Diverge (skipn 0 against) (skipn 0 lookahead)

main: A B C
against: A E
lookahead: A B
lookahead = (firstn 2 main)
EqDivergesAt :=
  TotalAlign (firstn 1 against) (firstn 1 lookahead)
  /\ Diverge (skipn 1 against) (skipn 1 lookahead)

main: A B
against: A B C
lookahead: A B
lookahead = (firstn 2 main)
EqDivergesAt :=
  TotalAlign (firstn 1 against) (firstn 1 lookahead)
  /\ Diverge (skipn 1 against) (skipn 1 lookahead)





a correct lookahead is one that, for some nodes/node lists A and B
- the lookahead head matches A
- if a token stream would match A ++ B, then the lookahead will say yes
- if a token stream would not match A ++ B (but only B?) then it will say no. probably that means that it simply *doesn't* match B??


if the lookahead matches B, then it also must *totally* match A, implying that A is subsumed by B
otherwise, it must not match B but only A
this means there are two ways to construct evidence that a lookahead is correct
- it matches A but not B
- it matches A and B, but B subsumes A

LookaheadCorrect L A B := forall stream, LookaheadYes L A B stream <-> NodeListMatches (A ++ B) stream





If the stream is:

- merely A, does the lookahead match? my first impulse is yes, although whether the *surrounding rule* will match is a much more fraught question
-


now it's all about how to define a "maximal" match
that's what defines a correct lookahead, it will tell us whether to take the current option in such a way that the overall match we produce will be maximal
now just what is maximal????



let's say we have a rule like this that we need to generate lookaheads for
what we really want to know is what lookahead do we need to test when we hit A B
a consume is all or nothing
(A B)? (A)

the lookahead has to be (A B), since merely (A) would falsely enter the ? consume if the













// E = (E (* | +))? B
// B = 0 | 1

// E = . (E (* | +))? B
// E = (E . (* | +))? B
// E = (E (* | +))? . B
// E = (E (* | +))? B .


// E = E + B
// E = B
// B = 0


// E = . E + B
// E = . B
// in both of these, we simply need to match any of the starting sequences of either E or B, which is only 0 here

// B = . 0
// this is similar, but we don't have to recurse

// E = E . + B
// here I think this means we've already reduced some E, and we just need to test +
// this contrasts with the below: *the decision to reduce E is dependent on seeing the +!*
// E = B .

// E = E + . B
// we've already tested for +, now just require B

// E = E + B .
// E = B .
// in both of these we can reduce E

// B = 0 .
// here we can reduce B





// here's a motivating example of where we could decide to reduce to a different ast node based on the lookahead
// :num = #num+
// :ident = #alpha+
// pattern = [(:ident ('=' :num)?)*]
// array = [:ident*]
// destructure = pattern '=' :num
// expression = array '+' :num
// statement = destructure | expression

// in order to parse a statement, we need to generally know whether we're about to encounter a pattern or an array

// it all comes down to those states in which what to do next isn't merely determined by what's in front of us, but also what's behind us




// the things we're trying to figure out:
// - how do we decide what decidables to attempt to match?
// - once we've matched some decidable, what next?
// - when do we call a reducer function?


// as some hint about how to handle different starting rules, every production where the marker is at the beginning has something to do with it
// another hint, having some "what comes after many of this" function would be helpful in doing lookahead past a many



const zero = /^0/
const one = /^1/

type E = { initial?: { E: E, op: '*' | '+' }, B: B }
type B = '0' | '1'

const reducers = {
  E(initial: E['initial'], B: E['B']): E {
    const e = { initial, B }
    console.log(e)
    return e
  },
  B(B: B): B {
    return B
  },
}
type reducers = typeof reducers


function parseE(): ReturnType<reducers['E']> {
  //
}



// let source = '0 1'

// const queue: string[] = []
// while (true) {
//  const current = queue.pop()
//  // first we need to know what lookaheads to test
//  // that should come from our current state?

//  if (current === undefined) {
//    // something about the entry state
//  }

//  source = source.trim()
// }

// function createReducers<Ctx, Grammar extends Dict<any[]>>(
//  reducers: { [K in keyof Grammar]: (args: [...Grammar[K], Ctx]) =>  },
// ) {
//  //
// }
