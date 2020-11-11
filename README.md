Peppermint Prover
=================

_A fresh interactive theorem prover_

(Also home of the [unfix-binders](unfix-binders/) library for a while)

## A warning ##

I wrote this README before being distracted by another project. When I
came back to this, I had a completely different idea of what I wanted
to do. Namely a more innovative theorem prover with a less innovative
architecture.

I don't really know what I'm getting at yet, so I'm not rewriting the
README for the time being. But whatever is below is likely to be out
of date.

You can follow the development of these idea on
[twitch.tv/notnotarnaud](https://twitch.tv/notnotarnaud), where I
livecode roughly fortnightly. You can also catch up on previous
streams on my [Youtube
channel](https://www.youtube.com/channel/UC1J0yq5gCrL6hAODvn67nYg),
which I update irregularly.

## Why ##

The world certainly doesn't need another proof assistant. There are
plenty great ones out there for all your computer-checked proving
needs (such as [Coq][coq], [Isabelle][isabelle], [Agda][agda], or
[Lean][lean], to name a few). To be perfectly blunt: I simply needed a
side project, and I happen to like writing and designing proof
assistants.

I've been thinking of dependently typed linear logic [for a
while][dissect-l]. My interest was greatly revived by Michael
Schulman's [remarkable analysis][ll-constructive-maths] of the
connection between linear logic and the constructive mathematics praxis.

### On the choice of foundation ###

I favour dependent type theory over more traditional logics, such as
HOL, mainly for one reason: I like to _abstract all the things_, and
dependent type theory offers a framework to do just that.

## Design ##

### Language ###

The language basically follows [my ideas][dissect-l] on dependent
linear types, though [McBride's][mcbride-rig] and [Atkey's][atkey-qtt]
more recent work on so-called quantitative type theory greatly improve
the theory. I'm following the style of [Linear
Haskell][linear-haskell] rather than that of quantitative type theory
because I believe it to work better. However, it seems to me that
values (of positive type) should maybe have a forward analysis in the
style of quantified type theory, rather than the backward analysis
that computations (of negative types) seem to require.

Putting these preliminary thoughts together, Peppermint

- is a sequent calculus (based on system L), because
    - Sequent calculus is closer to interactive proofs than natural
      deduction, hence basic tactics will be easier to write
    - I learnt from [Lengrand][lengrand-thesis] that dependently typed
      unification is made significantly easier in sequent calculus
    - I believe sequent calculus to be a sturdier (and, I confess,
      more fun) foundation than natural deduction
- is based on "classical" linear logic (that is, it sports an involutive
  dualisation operations)
    - This is needed in Schulman's analysis (though Schulman's logic is
      affine, and I'm not entirely sure yet how the analysis carries
      over to proper linear logic)
- has dependent elimination. In particular Π-types are inhabited by
  linear functions.
    - Without dependent elimination most of the properties of dependent
      type I'm interested in for reasoning disappear
- is polarised (that is values have positive types and computations
  have negative types), with explicit shifts. Like call-by-push-value,
  variables only have positive types.
    - It seems to solve many problems related to linear dependent
      elimination, especially in presence of duality.
    - On the other hand it makes it less obvious how to have
      judgemental computations. It's part of the exploration goals
      to try and pin this down.
- has anonymous least and largest fixed point construction for types
  (respectively, anonymous recursive terms).
    - It certainly comes with its own set of problems (mostly
      inscrutable type error messages), but it's cheaper to implement
      (plus, it fits better the implementation philosophy below).
    - It should make it easier to write type-generating code (such as
      Coq's [parametricity plugin][coq-parametricity]).

Clearly the design is not particularly justified, mostly it's what I
want to do, rather than what needs to be done. So be it.

Some non-logic considerations:

- Peppermint is an interactive prover in the style of [Coq][coq] in
  that proofs are elaborated with a tactic language
- The tactic language is an extension of the Peppermint logical
  language
- Peppermint terms (proofs and types) can contain holes aka
  metavariables aka existential variables. These holes can play
  various roles (to be automatically solved by the type inference
  mechanism, to be elaborated by interactive proofs, …), as a
  consequence holes have structure (I call it the hole language) which
  allows to specify what the programmer expects of the hole.
    - For instance the programmer can specify that the hole under
      consideration must be solved by a particular tactic `t` (I
      believe [Idris][idris] has something like this, too)

### Implementation ###

As a general consideration, I don't have an enormous amount of time to
dedicate to this project, so I favour everything that can gain me some
time. I intend this project to be innovative and exploratory only on
the narrow set of aspects such as the logic and, to some degree, the
logic's implementation.

For the rest, I will prefer off-the-shelf components. I'll also try to
use bidirectional parser/pretty-printer rather than give myself a lot
of flexibility on either end. I also favour types and structure over
efficiency. Incidentally, it's also why this program is written in the
Haskell programming language: while for a more large-scale effort I
would probably prefer Ocaml, Haskell is unique in the short-cuts it
offers, and will more realistically get Peppermint off the ground.

To sketch a more detailed design of the implementation, Peppermint is
implemented as various layers, each concerned with extending the logic
with extra stuff. At this early stage, I don't have yet a precise run
down of the specific layers that Peppermint will have (or the API of
Peppermint-the-library). But, here are some example of layers:

- The very bottom layer only understands a single expression. There is
  no way to break an expression into several top-level
  definitions. There are let-binders, of course, but that's about
  all. This layer can only type-check terms.
- Definitions are added in a further layer. But we can only type-check
  definition at this point.
- A further layer will add existential variables and type inference.

A layer can add elements which are recursive with previous layer
elements (_e.g._ adding let-binders to a layer that only understands
lambdas), because they are defined by open recursion (that is,
recursive types are defined as the least fixed point of a functor
which is materialised, and functions which would normally recurse over
that type are defined as algebra of the structure functor).

I intend the peppermint executable to give access to several (but
probably not all) of the layers.

As a last note: it is not the intention that the proofs always be
verified by the lowest layer. This is a point on which the design
differs radically than that of [Coq][coq]. In particular, proofs
interactively elaborated, by tactics, as terms with existential
variables are not rechecked in a notional kernel at "qed" time. I am,
however, considering giving the possibility of translating
developments from a layer to lower layers, for the sake of heightened
confidence (it is not, however, necessary, that all features which are
not in the lowest layer can be eliminated).
