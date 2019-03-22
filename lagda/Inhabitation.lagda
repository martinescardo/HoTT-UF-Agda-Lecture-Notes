---
layout: default
title : Introduction to Univalent Foundations of Mathematics with Agda
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

<!--
\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module Inhabitation where

open import Universes
open import MLTT-Agda
open import HoTT-UF-Agda
open import FunExt
\end{code}
-->

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="truncation"></a> Subsingleton truncation

The following is Voevosky's approach to saying that a type is
inhabited in such a way that the statement of inhabitation is a
subsingleton, using funext.

\begin{code}
is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P
\end{code}

This says that if we have a function from `X` to a subsingleton `P`, then
`P` must have a point. So this fails when `X=𝟘`. Considering `P=𝟘`, we conclude
that `¬¬ X` if `X` is inhabited, which says that `X` is non-empty. However,
in the absence of excluded middle, [inhabitation is stronger than
double negation](https://lmcs.episciences.org/3217).

For simplicity in the formulation of the theorems, we assume global
`dfunext`.

\begin{code}
global-dfunext : 𝓤ω
global-dfunext = ∀ 𝓤 𝓥 → dfunext 𝓤 𝓥

inhabitation-is-a-subsingleton : global-dfunext → (X : 𝓤 ̇ ) → is-subsingleton (is-inhabited X)
inhabitation-is-a-subsingleton {𝓤} fe X =
  Π-is-subsingleton (fe (𝓤 ⁺) 𝓤)
    λ P → Π-is-subsingleton (fe 𝓤 𝓤)
           (λ (s : is-subsingleton P)
                 → Π-is-subsingleton (fe 𝓤 𝓤) (λ (f : X → P) → s))

pointed-is-inhabited : {X : 𝓤 ̇ } → X → is-inhabited X
pointed-is-inhabited x = λ P s f → f x

inhabited-recursion : (X P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion X P s f φ = φ P s f
\end{code}

Although we [don't necessarily have](Appendix.html#moreexercices) that
`¬¬ P → P`, we do have that `is-inhabited P → P` if `P` is a subsingleton:

\begin{code}
inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ ) → is-subsingleton P → is-inhabited P → P
inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s id

inhabited-functorial : global-dfunext → (X : 𝓤 ⁺ ̇ ) (Y : 𝓤 ̇ )
                     → (X → Y) → is-inhabited X → is-inhabited Y
inhabited-functorial fe X Y f = inhabited-recursion
                                  X
                                  (is-inhabited Y)
                                  (inhabitation-is-a-subsingleton fe Y)
                                  (pointed-is-inhabited ∘ f)
\end{code}

This universe assignment for functoriality is fairly restrictive, but is the only possible one.

With this notion, we can define the image of a function as follows:

\begin{code}
image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image f = Σ \(y : codomain f) → is-inhabited (Σ \(x : domain f) → f x ≡ y)
\end{code}

*Exercise.* An attempt to define the image of `f` without the
inhabitation predicate would be to take it to be
`Σ \(y : codomain f) → Σ \(x : domain f) → f x ≡ y`. Show that this
type is equivalent to `X`. This is similar to what happens in set
theory: the graph of any function is isomorphic to its domain.


We can define the restriction and corestriction of a function to its
image as follows:

\begin{code}
restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
            → image f → Y
restriction f (y , _) = y

corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → X → image f
corestriction f x = f x , pointed-is-inhabited (x , refl (f x))
\end{code}

And we can define the notion of surjection as follows:
\begin{code}
is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection f = (y : codomain f) → is-inhabited (Σ \(x : domain f) → f x ≡ y)
\end{code}

*Exercise.* The type `(y : codomain f) → Σ \(x : domain f) → f x ≡ y`
 is equivalent to the type `has-section f`, which is stronger than
 saying that `f` is a surjection.

There are two problems with this definition of inhabitation:

  * Inhabitation has values in the next universe.

  * We can eliminate into propositions of the same universe only.

In particular, it is not possible to show that the map `X →
is-inhabited X` is a surjection, or that `X → Y` gives `is-inhabited X
→ is-inhabited Y` for `X` and `Y` in arbitrary universes.

There are two proposed ways to solve this:

  * Voevodsky works with certain [resizing
    rules](http://www.math.ias.edu/vladimir/files/2011_Bergen.pdf) for
    subsingletons. At the time of writing, the (relative) consistency
    of the system with such rules is an open question.

  * The HoTT book works with certain higher inductive types (HIT's),
    which are known to have models and hence to be (relatively)
    consistent.  This is the same approach adopted by cubical type
    theory and cubical Agda.

A third possibility is to work with propositional truncations
[axiomatically](https://lmcs.episciences.org/3217), which is compatible
with the above two proposals. We write this axiom as a record type
rather than as an iterated `Σ-type` for simplicity, where we use the
HoTT-book notation `∥ X ∥` for the inhabitation of `X`,
called the propositional truncation of `X`:

\begin{code}
record propositional-truncations-exist : 𝓤ω where
 field
  ∥_∥          : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-a-prop : {𝓤 : Universe} {X : 𝓤 ̇ } → is-prop ∥ X ∥
  ∣_∣          : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-rec       : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
              → is-prop P → (X → P) → ∥ X ∥ → P
\end{code}

This is the approach we adopt in our [personal Agda
development](http://www.cs.bham.ac.uk/~mhe/agda-new/).

We now assume that propositional truncations exist for the remainder
of this file, and we `open` the assumption to make the above fields
visible.

\begin{code}
module basic-truncation-development
         (pt : propositional-truncations-exist)
         (fe : global-dfunext)
       where

  open propositional-truncations-exist pt public

  ∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
  ∥∥-functor f = ∥∥-rec ∥∥-is-a-prop (λ x → ∣ f x ∣)

  ∃ : {X : 𝓤 ̇ } → (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃ Y = ∥ Σ Y ∥
\end{code}

The propositional truncation of a type and its inhabitation are
logically equivalent propositions:

\begin{code}
  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇ ) → ∥ X ∥ ⇔ is-inhabited X
  ∥∥-agrees-with-inhabitation X = a , b
   where
    a : ∥ X ∥ → is-inhabited X
    a = ∥∥-rec (inhabitation-is-a-subsingleton fe X) pointed-is-inhabited
    b : is-inhabited X → ∥ X ∥
    b = inhabited-recursion X ∥ X ∥ ∥∥-is-a-prop ∣_∣
\end{code}

Hence they differ only in size, and when size matters don't get on the
way, we can use `is-inhabited` instead of `∥_∥` if we wish.

*Exercise*. If `X` and `Y` are types obtained by summing `x-` and
  `y`-many copies of the type `𝟙`, respectively, as in `𝟙 + 𝟙 + ... + 𝟙` , where `x`
  and `y` are natural numbers, then `∥ X ≡ Y ∥ = (x ≡ y)` and the type
  `X ≡ X` has `x!` elements.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="choice"></a> The univalent axiom of choice

\begin{code}
  AC : ∀ 𝓣 (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X → ((x : X) → is-set (A x)) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥  ̇
  AC 𝓣 X A i j = (R : (x : X) → A x → 𝓣 ̇ )
               → ((x : X) (a : A x) → is-prop (R x a))
               → ((x : X) → ∃ \(a : A x) → R x a)
               → ∃ \(f : (x : X) → A x) → (x : X) → R x (f x)

  Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
  Choice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ )
             (i : is-set X) (j : (x : X) → is-set (A x))
           → AC 𝓤 X A i j
\end{code}

This axiom is relatovely consistent, because Voevodsky's
[simplicial-set model](https://arxiv.org/abs/1211.2851) validates
it. But it is important that we have the condition that `A` is a
set-indexed family of sets. For general higher groupoids, it is not in
general possible to perform the choice functorially. This is
equivalent to another familiar formulation of choice, namely that a
set-indexed product of non-empty sets is non-empty, where in a
constructive setting we generalize `non-empty` to `inhabited`.

\begin{code}
  IAC : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
      → is-set X → ((x : X) → is-set (Y x)) → 𝓤 ⊔ 𝓥 ̇
  IAC X Y i j = ((x : X) → ∥ Y x ∥) → ∥ Π Y ∥

  IChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  IChoice 𝓤 = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
             (i : is-set X) (j : (x : X) → is-set (Y x))
            → IAC X Y i j
\end{code}

These two forms of choice are logically equivalent (and hence
equivalent, as both are subsingletons assuming function
extensionality):

\begin{code}
  Choice-gives-IChoice : Choice 𝓤 → IChoice 𝓤
  Choice-gives-IChoice {𝓤} ac X Y i j φ = γ
   where
    R : (x : X) → Y x → 𝓤 ̇
    R x y = x ≡ x -- Any singleton type in 𝓤 will do.
    k : (x : X) (y : Y x) → is-prop (R x y)
    k x y = i x x
    h : (x : X) → Y x → Σ \(y : Y x) → R x y
    h x y = (y , refl x)
    g : (x : X) → ∃ \(y : Y x) → R x y
    g x = ∥∥-functor (h x) (φ x)
    c : ∃ \(f : Π Y) → (x : X) → R x (f x)
    c = ac X Y i j R k g
    γ : ∥ Π Y ∥
    γ = ∥∥-functor pr₁ c

  IChoice-gives-Choice : IChoice 𝓤 → Choice 𝓤
  IChoice-gives-Choice {𝓤} iac X A i j R k ψ = γ
   where
    Y : X → 𝓤 ̇
    Y x = Σ \(a : A x) → R x a
    l : (x : X) → is-set (Y x)
    l x = subsets-of-sets-are-sets (A x) (R x) (j x) (k x)
    a : ∥ Π Y ∥
    a = iac X Y i l ψ
    h : Π Y → Σ \(f : Π A) → (x : X) → R x (f x)
    h g = (λ x → pr₁ (g x)) , (λ x → pr₂ (g x))
    γ : ∃ \(f : Π A) → (x : X) → R x (f x)
    γ = ∥∥-functor h a
\end{code}

For more information with Agda code, see
[this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-Choice.html), which
in particular has a proof that univalent choice implies univalent
excluded middle.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="sip"></a> Structure identity principle

For the moment, see [this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-StructureIdentityPrinciple.html).

[<sub>Table of contents ⇑</sub>](toc.html#contents) [<sub>Appendix ⇓ </sub>](Appendix.html)
