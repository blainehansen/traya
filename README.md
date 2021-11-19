# :warning: this repo is dormant for now :warning:

This project is one of many on a long and painful quest to close soundness gaps in the software ecosystems I work in, and make all the tools I use completely typesafe. [Read about the journey in this blog post.](https://blainehansen.me/post/my-path-to-magma/)

This project is dormant for now as I build the [Magma proof checker](https://github.com/blainehansen/magma), but I might return to it and use Magma to take it to the next level.

Feel free to check out the rough unfinished documentation below.

---

things we want:

- "reducer" functions that are simply called with their children after the parser is sure that rule matches
- a simple "peg" style grammar definition with |*+? instead of multiple production rules, and ideally no need for "until" or "not before"
- able to start from any rule, allowing rules to be called for different purposes (can parse a whole file, or just an expression)
- able to automatically generate "obvious" abstract and concrete syntax trees that merely conform directly to the grammar
- able to account for "greedy" situations, and make decidables smart enough to handle them. especially I'm worried about greedy tails, since that has surprised me several times. at the very least we want to warn about these things
- as much as possible is static, this is a type-safe generator in more ways than one
- the more flexible and powerful the better

https://tupl.cs.tufts.edu/papers/itp2019_ll1.pdf
https://en.wikipedia.org/wiki/LL_parser#Constructing_an_LL(k)_parsing_table
http://www.cs.ecu.edu/karl/5220/spr16/Notes/Top-down/index.html
https://gallais.github.io/pdf/agdarsec18.pdf

https://www.antlr.org/papers/allstar-techreport.pdf
Although it sounds nice to have direct left-recursion, the ast structure really ought to have interesting different forms for different constructions.

So I want to use coq to specify how the ast of kreia works, and how it is processed and validated. Then I can use it to understand the algorithms, properties, and optimizations I can apply. Of particular interest is computing decidables for decision points, especially in the presence of greediness. A rule or macro that has a potentially greedy tail needs to accept and use a decidable computed based on the particular context it occurs in.


A redo of the json parser:

```kreia
:str = '"' ('\\' ["\\] | ^[\n"\\])* '"'
:num = [0-9]+ ('.' [0-9]+)?
:atom = 'null' | 'undefined' | 'true' | 'false'
:comma = ","
:whitespace _= #whitespace+

json =
  | array
  | object
  | primitive

@manySeparated[$body, $sep] = $body ($sep $body)*
@separatedByCommas[$def] = @manySeparated[$def, _:comma]

array = "[" @separatedByCommas[json]? "]"

object = "{" @separatedByCommas[key json]? "}"

primitive =
  | :str
  | :num
  | :atom

key = :str ":"
```

```ts
// in a macro-ts world someday!
import { ParserCreator } from kreia!!('./json')

type Json =
  | JsonPrimitive
  | JsonObject
  | JsonArray
type JsonPrimitive = string | number | boolean | null | undefined
type JsonObject = { [property: string]: Json }
type JsonArray = Json[]

const parser = ParserCreator({
  json(primOrObjectOrArray): Json {
    return primOrObjectOrArray
  },

  array(items): JsonArray {
    return items
  },

  object(entries): JsonObject {
    const give: JsonObject = {}
    for (const [key, value] of entries)
      give[key] = value
    return give
  },

  primitive(tok): JsonPrimitive {
    switch (tok.type.name) {
      case 'str':
        return tok.content.slice(1, -1)
      case 'num':
        return tok.content.includes('.')
          ? parseFloat(tok.content)
          : parseInt(tok.content)
      case 'atom':
        switch (tok.content) {
          case 'null': return null
          case 'undefined': return undefined
          case 'false': return false
          case 'true': return true
        }
    }
  },

  key(strToken): string {
    return strToken.content.slice(1, -1)
  },
})

const okObject = parser.json(`{
  "yo": null,
  "here": 4,
  "different": ["stuff", 5, undefined, true],
  "while": {
    "nested": {
      "again": "sdf"
    }
  }
}`)

const okNull = parser.json('null')
const okArray = parser.json('[5, 4, 3, "yo yo yo"]')
const errJson = parser.json('5, 4')

const okPrimitive = parser.primitive('true')
const errPrimitive = parser.primitive('yoyo')


// NOTE: rather than always generating these forms, it's probably a better idea to choose at generation time which variants to produce
// most people won't use these concrete variants

// includes all tokens and all spans, even ignored ones, represented as tuples (what would we name everything?)
const okFull = ParserCreator.ConcreteSyntaxTree('null')

// same as above but ignores globally ignored tokens
const okUserIgnored = ParserCreator.ConcreteSyntaxTree('null', { ignoreGlobal: true })

// same as above but ignores everything
const okFull = ParserCreator.ConcreteSyntaxTree('null', { ignoreGlobal: true, ignoreAnonymous: true, ignoreMarked: true })
```
