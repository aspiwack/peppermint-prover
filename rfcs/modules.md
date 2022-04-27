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

Another consequence of coherence is the sometimes confusing semantics
of type-class instance resolution. I've seen even seasoned Haskell
programmers get confused, on occasions, by the fact that

```haskell
instance C x => D (F x)
```

doesn't mean that “whenever `C x` holds, then `D (F x)` holds”, but
rather “in order to prove that `D (F x)`, you _must_ prove `C x`”. In
other words, which may or may not make more sense to you, depending on
where you're coming from, `C x` is a proof obligation, not a
condition.

I should really find an example of a place where this is confusing,
but I can't recall a concrete instance. I remember having observed
such a confusion pretty recently, but I don't remember the context at
all. Ah well… I'll edit when another one comes up.

### Subtyping

Another notable difference between type classes and modules is their
approach to subtyping: type classes use nominal subtyping, and modules
use structural subtyping.

That is, when I write

```haskell
class Applicative m => Monad m where
  …
```

I'm stating that the class named `Monad` is a subclass of the class
named `Applicative` (as an aside, the `=>` here stands for reversed
implication: it's being a monad which implies being an applicative,
not the other way around; whereas `=>` appropriately represents an
implication in instance declarations. I'm not sure how that came to
be, historically, but it's an unfortunate accident). If I were to
define a clone of `Applicative`:

```haskell
class Functor f => Applicative' f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
```

Then `Applicative'` and `Monad` would be unrelated.

Whereas in modules, a module type `T1` is a subtype of another module
type `T2` _because_ `T1` contains all the definitions of `T2`. The
names of the module types play no role.

This is the same distinction as the subclassing in Java, where the definition

```java
class MyClass inherits SuperClass {
  …
}
```

declares (maybe we should rather say “decrees”) that the class
`MyClass` is a subclass of `SuperClass`, versus the subclassing in
Ocaml via row type unification (classes in Ocaml are just object
generators, they are not types).

To be clear, I don't think that this distinction is essential to the
mechanisms of type classes and modules, we could most certainly create
type classes with structural subtyping and modules with nominal
subtyping. I don't think it would affect their essence too much,
really.

But I'm raising this difference because it's an axis in the design
space, and it needs discussing. What is happening, really, is that I'm
kind of taking side for structural subtyping here. It's because of the
problem of _hierarchy expansion_.

I came up with the term “hierarchy expansion” as I wrote these
lines. But I'm not aware of an established term for the problem. If
there is, please make a pull request and I'll use it instead;
otherwise I'm calling dibs.

The problem of hierarchy expansion is when you have a hierarchy of
classes (or module types), by which I mean a (semantically coherent, I
expect) lattice of classes (for the subtyping order). And then you
want to insert a new class in the middle.

A prominent example of this is the [Functor-Applicative-Monad
Proposal][AMP] (lovingly known as the AMP)for Haskell's standard
library, which added the `Applicative` type class in-between `Functor`
and `Monad`.

In a nominal-subtyping setting, this is miserable: every monad
definition (there are a lot in Haskell code) must now talk about
`Applicative`. There is no way around it. Many, many libraries must be
modified to include this (they can be modified ahead of time to be
forward compatible, but it's still a pain, and it was a difficult
transition (it was before my time as an active Haskell programmer, so
I don't really have war stories, though)).

With structural subtyping, it can be as simple as naming a new subset
of the definitions from a module type in the hierarchy (this is free),
or, more often, adding a few definitions to that type, and naming a
subset of the augmented type. This isn't sufficient by itself, but the
problems are considerably smaller. With a system of default
implementations, we can make the hierarchy expansion backward
compatible.

And, really, when you think about it: just naming a new intermediate
concept ought to be backward compatible. Monads don't stop being
monads because you've identified that the superset of applicative
functors is of interest.

### Matchability

This last point is somewhat theoretical, and it's another issue that
I'm having with type class. Which is that application of type
variables is what Richard Eisenberg has been calling matchable. Namely
that if `f a ~ g b` then `f ~ g ∧ a ~ b`. It basically says that every
type variable stands for a type constructors, it precludes the
existence of a type-level λ (because otherwise `f = λx. b` and
`g=λx. x` are a solution of the former equation, but not the latter
pair).

Why must we have matchability when we do type-class style inference?
Consider `fmap`:

```haskell
fmap :: Functor f => (a -> b) -> f a -> f b
```

Without matchability, we could never unify `f b` or `f a` with
anything: the variable `f` would be ambiguous in this expression. So
we would have to provide the value of `f` every time we call
`fmap`. It's not necessarily a terrible thing, though it runs contrary
to the spirit of type classes. And, at any rate, it is weird that I'd
have to specify the type of functors systematically, but not of
monoids. In Haskell, specifically, the “do” notation relies heavily on
the fact that the type of functors (monads, even, in this case) can be
inferred. Matchability is heavily baked in Haskell's design, and
frankly, I don't think that a type-class system without matchability
would be palatable (unless we don't have higher-kinded type, of
course).

Compare with the same function, but with modules instead:

```ocaml
F.map : ('a -> 'b) -> 'a F.t -> 'b F.t
```

Here we don't need a type variable for the functor: it is fixed by the
module name which is passed explicitly by design. So we don't need
matchability either.

An immediate consequence of matchability is that with type classes it is
impossible to say something like

```haskell
instance (Functor f, Functor g) => Functor (λx. f (g x))
```

since there is no type-level λ. Instead we have to a subterfuge:

```haskell
newtype Compose f g a = Compose (f (g a))

instance (Functor f, Functor g) => Functor (Compose f g)
```

Ugh! These newtype annotations again: even if we get rid of coherence,
matchability forces newtype annotations on us. This isn't a problem in
module style: you still need a name `Compose` but it's only a module
name, the resulting types unify as you expect.

```ocaml
module Compose (F:Functor) (G:Functor) : Functor = struct
  type 'a t = 'a G.t F.t
  
  map f x = F.map (G.map f) x
end
```

Though, of course, you end up having the same problem as with
`PairMonoid` above. This module is really `FunctorCompose`, and, in
Ocaml, you would also have `ApplicativeCompose`, and
`TraversableCompose`. Which really can't be called great, even with a
lot of creativity.

I've had, for a while, in the back of my mind the idea of extending
Haskell's unification with a λ without compromising matchability.
Using pattern unification (see, for instance, [this
article][pattern-unification]). However, I now consider this unlikely
to work, because pattern unification specifically tries to avoid terms
of the form `f a`, where both `f` and `a` are unification variables:
pattern unification really wants `f` to be a type constructor. I think
that in the module style, since we are usually able to avoid `f a`, we
could leverage pattern unification. I'm not sure that it is worth it,
but it'd be comforting to know that it's a plausible extension.

This matchability story, by the way, is the reason why type synonyms
and type families must be fully applied: a partially applied type
family isn't matchable, so at the very least it can't be substituted
for a variable which is assumed to be matchable. There is a solution
in the Haskell world: record in the kind of (higher-kinded) type
variables whether they are matchable or not (see [the
article][matchability] or [the proposal][unsaturated-type-families]
for more details). While I'm convinced that this idea of
matchability-in-the-type is the way forward for Haskell, this is a
complexity that I'd rather avoid in the future.

Now, I haven't been completely honest in this section. It is true that
the module style largely releases us from the need to unify type
variable applications (`f a`). So we don't need to assume that type
variables are matchable. But I don't think that we would go very far
in module definitions, if an abstract `F.t` (like in the `Compose`
example above) didn't have the property that `'a F.t ~ 'b F.t` implies
`'a ~ 'b`. This property is weaker than matchability (it's called
injectivity), but it is not verified by arbitrary computations (what
Haskell calls _type families_).

Does it mean that functor types cannot be arbitrary computations (they
could still be patterns in the sense of pattern unification, though)?
It's a plausible restriction, but it's also quite arbitrary. There is
no mathematical reason to ban computing a functor type. Nor for a
functor to be injective (`λx. unit` is a functor, mathematically). But
we are not able to make this assumption, I fear that writing
higher-order modules, like `Compose` may be pretty annoying, with a
lot of type annotations. This is likely to trump newcomers, too. I
can't say that I have a good answer at the moment. It's definitely
something to be mindful of.

## Design

### Terminology

Writing in progress.

- unification variables
- member

### Difficulties

TODO: describe

```haskell
traverse :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
```

How do I convert it in module style? Specifically how do I name the
`f` parameter (if I don't have matchability)?

[modular-implicits]: https://arxiv.org/abs/1512.01895
[newtype-rant]: https://twitter.com/aspiwack/status/1471224270114197512
[dictionary-application]: https://arxiv.org/abs/1807.11267
[coerce-representational]: https://dl.acm.org/doi/abs/10.1145/2628136.2628141
[higher-order-roles-proposal]: https://github.com/ghc-proposals/ghc-proposals/pull/233
[type-role-set-nominal]: https://github.com/haskell/containers/blob/90da499c6703820e31ce4b631a22bad01e443dfb/containers/src/Data/Set/Internal.hs#L283
[dictionary-application]: http://arxiv.org/abs/1807.11267v1
[AMP]: https://wiki.haskell.org/Functor-Applicative-Monad_Proposal
[unsaturated-type-families]: https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0242-unsaturated-type-families.rst
[matchability]: https://dl.acm.org/doi/abs/10.1145/3341706
[pattern-unification]: https://link.springer.com/article/10.1007/s10472-021-09774-y
