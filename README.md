# Monads in functional programming: a formalized proof of their equivalence with Kleisli triples **(Lean Version)**

“Being a language, mathematics may be used not only to inform but also, among other things, to seduce.”
─Benoît Mandelbrot


“There is no branch of mathematics, however abstract, which may not some day be applied to phenomena of the real world.”
─Nikolai Ivanovich Lobachevsky


“Category theory is a relatively young branch of pure mathematics that most computer scientists would consider esoteric”
─Benjamin C. Pierce


This repository contains the Lean translation of my work toward a computer science degree. My thesis is [here](http://132.248.9.195/ptd2016/junio/0746652/Index.html).

[The original work formalized basic concepts of category theory in Coq](https://github.com/spidermoy/Monads_KleisliTriples_Proof).
This version translates the definitions and proofs into [Lean](https://lean-lang.org/).

---

## A few history

The notion of monad was invented by Roger Godement in 1958 under the name
"standard construction." In the 1960s and 1970s, many people used the name
"triple." The now standard term "monad" is due to Saunders Mac Lane.
(See [Monad](https://en.wikipedia.org/wiki/Monad_(category_theory)#Overview))

Eugenio Moggi was the first to explicitly link the monad of category theory to
functional programming. In earlier work, several computer scientists
had advanced using category theory to provide semantics for the lambda calculus.
Several others popularized and built on this idea, including Philip Wadler and
Simon Peyton Jones, both of whom were involved in the specification of Haskell.
At first, programming with monads was largely confined to Haskell and its derivatives,
but as functional programming has influenced other paradigms, many languages have
incorporated a monad pattern (in spirit if not in name).
Formulations now exist in Scheme, Perl, Python, Racket, Clojure, Scala, F#,
and have also been considered for a new ML standard.
(See [Monad (functional programming)](https://en.wikipedia.org/wiki/Monad_(functional_programming)))

The more common definition for a monad in functional programming is actually
based on a Kleisli triple rather than category-theory's standard definition.
The two constructs turn out to be mathematically equivalent.
(See [Kleisli Triple](https://en.wikipedia.org/wiki/Kleisli_category))

In 1991, Moggi give us a small and informal proof of the mathematical equivalence
between monads and Kleisli triples.
(See [Moggi, E. (1991). Notions of computation and monads](https://www.disi.unige.it/person/MoggiE/ftp/ic91.pdf)).
In 2007, Gammon shows a detailed and extended formal proof of the mathematical equivalence
between monads and Kleisli triples.
(See [Gammon, S. C. (2007). Notions of category theory in functional programming (Doctoral dissertation, University of British Columbia).](https://open.library.ubc.ca/cIRcle/collections/ubctheses/831/items/1.0080357))
Finally, in 2016, I formalized Gammon's proof in the proof assistant Coq.

---

## Lean

Updated to run with Lean 4.35.0

This work contains:

    * Category definition
    * Category examples
    * Functor definition
    * Identity functor definition
    * Functors composition definition
    * Natural Transformation definition
    * Monad definition
    * Kleisli triple definition
    * Formalized proof of the mathematical equivalence between monads and Kleisli triples
