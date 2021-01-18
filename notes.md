https://xavierleroy.org/publi/validated-parser.pdf





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

// it all comes down to those states in which what to do next isn't merely determined by what's in front o fus, but also what's behind us




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
