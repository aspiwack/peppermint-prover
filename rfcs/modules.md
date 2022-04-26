# A module system proposal

## Type classes vs ML-style module

There are three big families of solutions to group definitions:
- Type classes (Haskell, Rust (traits), Coq, C++ (concepts), …)
- Modules, typically with “functors” (higher-order modules), or mixins
  (Ocaml, SML, Coq, Haskell's Backpack, …)
- Classes/objects (Java, C++, Ocaml, Javascript, Python, …)

In a sense, classes & objects are more a philosophy around which the
entire language is designed. I'm thinking of a functional language, so
I don't think I need to go this way. Ocaml's experience with objects
(they exist, but are basically unused) comforts me in the idea that
it's not really a good starting point.

We are left with type classes and modules. They both are great
sometimes, awful other. Let's try to compare them.

Type classes are great for their ability to generate code on the
fly. If I have, say

```haskell
instance Monoid A
instance Monoid B
instance (Monoid a, Monoid b) => Monoid (a, b)
```

Then I can use `(<>)` at type `(A, B)` without further code.

You can do the same with modules, but it's going to be pretty
painful. Maybe you have modules `A`, `B` both monoids, then you would
do something like `PairMonoid(A)(B).(<>)`. It's worth noting that a
generic `Pair` module could not be a monoid, since it would take
arbitrary `A` and `B` type, not only monoids. So you really need one
such module per structure. You could avoid having to name the module
using something like [modular-implicits] (more on that later).

I think that this difficulty of generating code is one obstacle to
having good algebraic hierarchies in Ocaml. And well, I care about
algebra. So it's a problem for me.

Another deficiency of modules, which I think is of similar nature, is
the lack of extensibility. Say I want to make a map with keys of type
`A`, it would naturally fit in a `A.Map` module. But if I made my
module `A` without a `Map` submodule, then it's over, you don't get to
add it. Whereas type classes are naturally extensible: the type takes
the role of the name, and we can attach any number of functions to it
after the fact. This leads Ocaml modules to be riddled with

```ocaml
module IntMap = Map.Make(Int)
…
```

or worse

```ocaml
module IntExt = module
  include Int
  module Map = Map.Make(Int)
end
```

It's really not great in practice.

On the other hand the implicitness of type classes is really a
problem. While it's usually clear in small examples what we are
referring to, in fact, in small examples, the implicitness of type
classes is clearly a strength, and the explicitness of modules feels
like noise. On actual code bases, it's really hard to know at what
types type classes are called. And it makes reading code quite a bit
of a puzzle game. It can be alleviated with tools that figure this out
for you, but it's still slower and more effort to read. I've seen that
being a problem in more than one occasion. And I personally don't feel
like I can easily read code with type classes. Sometimes, it does
require quite a lot of mental gymnastic.

A somewhat more subtle issue with type classes is that it doesn't
integrate well with IDE completion. Suppose that I'm writing Ocaml
code if I type `List.` as soon as I type the `.`, my completion engine
can give me the list of all the functions of the `List` module. On the
other hand, with type classes, there is nothing to start the
completion. This is not an intrinsic problem though, as it can be
solved using a `value.method` syntax like Rust's traits: as long as
the type of `value` can be inferred, then it can trigger the
completion with all the attached type classes. This is what most
completion engines do, considering the dominance of
object-oriented-like syntax in mainstream programming languages. So
it's a bit of a distraction, on the theoretical side, but something to
keep in mind for the practicality of the system.

extensibility of modules (or rather lack thereof)
type classes and newtypes, and coherence
modular implicit and coherence

[modular-implicits]: https://arxiv.org/abs/1512.01895
