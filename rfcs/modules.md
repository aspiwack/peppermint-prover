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

### Code generation

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

### Extensibility

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

### Explicitness

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

### Coherence and newtypes

Type classes strongly rely on a property called (global)
coherence. That is that for a given type `A`, there is at most one
instance of `SomeClass A`. It's central for two reasons:

- Predictability: we can know which instance was selected by the type
  inference mechanism
- Correctness of abstraction: if I define `union :: Ord a => Set a ->
  Set a -> Set a`, for instance, I am assuming that both sets were
  built with the same `Ord` instance. Which they are since there is at
  most one `Ord` instance for `a`. Actually, even when I do `add
  :: Ord a => a -> Set a -> Set a`, the set had better be built with
  the same `Ord` instance I'm currently using. Otherwise, I have no
  chance of making a binary search tree.

In contrast, ML modules will rely on abstract type. As such,
`Map.Make(Int).t` and `Map.Make(ReverseOrderInt).t` are two different
types. Which makes it so that they both have `add` and `union`
functions, which can't be mixed, despite having the same element
types. An adverse consequence of this is that it becomes impossible to
write a function `forall a b. (a -> b) -> Set a -> Set b` in Ocaml
whereas it's possible (even if not particularly efficient) in Haskell
(well, `forall a b. (Ord a, Ord b) => (a -> b) -> Set a -> Set b`).

The main problem with coherence is that if I need a different `Ord`
instance for a type `A`, I need to create a new type `A'` (since there
is at most one `Ord` instance for `A`), in Haskell this is typically
done with a `newtype` declaration:

```haskell
newtype A' = MkA' A
```

Whereas in Ocaml, you simply make a different module with the same
type:

```haskell
module A' = struct
  type t = A.t
  compare = …
```

The main problem with newtypes is that Haskell code often ends up
riddled with annotation to convert between equivalent types for the
sole sake of selecting instances. It really obscures the intent of the
code. Sometimes you write functions which are more newtype annotation
than actual code. It's really a pity. Here is me [ranting about
this][newtype-rant].

One (more theoretical) aspect of the centrality of this whole newtype
business, is that you will often want the newtype to share many
instances with the original type. Haskell has a deriving mechanism for
that. To do that, it deploys the so-called [representational
coercions][coerce-representational]. Coercions come in two forms in
Haskell: representational and nominal (the latter is
stronger). Argument of type constructors have roles (representational
or nominal); representational coercions can only be applied at
representational positions (whereas nominal can be applied to
both).

Which is quite the complication, theoretically, but also means
that if you have some nominal stuff going on in your type class, you
may not be able to derive it for newtypes (and for good reason: as far
as the compiler know, it may be unsafe). The
[paper][coerce-representational] explains very well why this is all
needed. Roles themselves have limitations in the current
understanding, in particular the [difficulty of assigning roles to
arguments of (higher-kinded) type
variables][higher-order-roles-proposal].

It is also worth noting that it may be very important to select roles
properly for abstract types. For instance, in `Set a`, `a` must be
nominal (otherwise, we could coerce to a newtype and break the
guarantees given by coherence as discussed above), but Haskell infers
that `a` is representational: so we need to manually restrict the type
([on this line][type-role-set-nominal]). This is quite easy to forget,
I'm willing to bet that there are a lot of partially enforced
abstractions in Haskell code for this very reason.

None of these problems exist with modules. You can happily switch
between the functions of two different modules while acting on the
same type.

I know of two ways to reduce the burden of newtype annotations. The
first one is [explicit dictionary
applications][dictionary-application]. In this approach, we keep the
type classes, but try to give them a little bit of the explicitness of
module: we pass explicit dictionaries (_i.e._ instances except not
used implicitly) to a function which is qualified by a type-class
constraint. The limitation of this approach is that it relies on roles
so inherits all that baggage. It's elegant, but I'm not really
convinced that it will pan out well in practice.

The other approach is [modular implicits][modular-implicits], which I
already mentioned above. Here we start with modules, and we give them
some of the implicit power of type classes. So you have modules, quite
normally, but you also have resolution rules which can be used to
discharge module constraints implicitly. This approach doesn't need
coherence for correctness, however, the experience of Scala 2 appears
to show that incoherent implicits are really hard to manage (my
understanding is that Scala 3 has moved to a coherent kind of implicit
resolution). What isn't convincing, to me, in this approach, is that
if we are to write modules as we write type classes, when we don't end
up in the canonical case, using explicit module will be very unpleasant
(in the style of `MonoidPair` above). Modules and type-classes are not
written the same: we want to write long exhaustive modules, but small
atomic type classes. I doubt trying to mix both styles will end up in
something harmonious.

At any rate, neither of this solution address my issues with
matchability (see below).

### Nominal vs Structural subtyping

### Matchability

The backward semantics is unintuitive

[modular-implicits]: https://arxiv.org/abs/1512.01895
[newtype-rant]: https://twitter.com/aspiwack/status/1471224270114197512
[dictionary-application]: https://arxiv.org/abs/1807.11267
[coerce-representational]: https://dl.acm.org/doi/abs/10.1145/2628136.2628141
[higher-order-roles-proposal]: https://github.com/ghc-proposals/ghc-proposals/pull/233
[type-role-set-nominal]: https://github.com/haskell/containers/blob/90da499c6703820e31ce4b631a22bad01e443dfb/containers/src/Data/Set/Internal.hs#L283
[dictionary-application]: http://arxiv.org/abs/1807.11267v1
