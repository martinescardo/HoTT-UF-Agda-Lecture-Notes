---
layout: default
title : Introduction to Homotopy Type Theory and Univalent Foundations (HoTT/UF) with Agda
date : 2019-03-04
---
## <a id="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

4th March 2019, version of {{ "now" | date: "%d %B %Y, %H:%M" }}.

[Martín Hötzel Escardó](http://www.cs.bham.ac.uk/~mhe/),
[School of Computer Science](https://www.cs.bham.ac.uk/),
[University of Birmingham](http://www.bham.ac.uk/),
UK.

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)

**Abstract.** We introduce [Voevodsky](http://www.math.ias.edu/Voevodsky/)'s [univalent foundations](http://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01616-9/) and
[univalent mathematics](https://github.com/UniMath/UniMath/blob/master/README.md), and explain how to develop them with the
computer system [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php), which is based on [Martin-Löf type theory](https://github.com/michaelt/martin-lof).
Agda allows us to write mathematical definitions, constructions,
theorems and proofs, for example in number theory, analysis, group
theory, topology, category theory or programming language theory, checking
them for logical and mathematical correctness.

Agda is a constructive mathematical system by default, which amounts
to saying that it can also be considered as a programming language for
manipulating mathematical objects. But we can assume the axiom of
choice or the principle of excluded middle for pieces of mathematics
that require them, at the cost of losing the implicit
programming-language character of the system.  For a fully
constructive development of univalent mathematics in Agda, we would
need to use its new [cubical
flavour](https://homotopytypetheory.org/2018/12/06/cubical-agda/), and
we hope these notes provide a base for researchers interested in
learning Cubical Type Theory and Cubical Agda as the next step.

Compared to most expositions of the subject, we work with explicit
universe levels.

**Keywords.** Univalent mathematics. Univalent foundations. Univalent
  type theory. Univalence axiom. `∞`-Groupoid. Homotopy type. Type
  theory. Homotopy type theory. Intensional Martin-Löf type
  theory. Dependent type theory. Identity type. Type
  universe. Constructive mathematics. Agda. Cubical type
  theory. Cubical Agda. Computer-verified mathematics.

**About this document.**
[This](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes) is a set
of so-called
[literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html)
Agda files, with the formal, verified, mathematical development within
*code* environments, and the usual mathematical discussion outside
them.
Most of this file is not Agda code, and is in markdown format, and the
html web page is generated automatically from it using Agda and other
tools. [Github](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes)
pull requests by students to fix typos or mistakes and clarify
ambiguities are welcome.
There is also a [pdf
version](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.pdf)
automatically generated from the [html version](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html).
These notes were originally developed for the
[Midlands Graduate School 2019](http://events.cs.bham.ac.uk/mgs2019/). They will evolve for a while.

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)
### <a id="introduction"></a> Introduction

A univalent type theory is the underlying formal system for a
foundation of univalent mathematics as conceived by [Voevodsky](http://www.math.ias.edu/Voevodsky/).

In the same way as there isn't just one set theory (we have e.g. [ZFC](https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory)
and [NBG](https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del_set_theory) among others), there isn't just one univalent type theory (we
have e.g. the underlying type theory used in [UniMath](https://github.com/UniMath/UniMath), [HoTT-book type
theory](https://homotopytypetheory.org/2015/01/07/the-hott-book-does-not-define-hott/), and [cubical type theory](https://arxiv.org/abs/1611.02108), among others, and more are expected
to come in the foreseeable future before the foundations of univalent
mathematics stabilize).

The salient differences between univalent mathematics and traditional,
set-based mathematics may be shocking at first sight:

 1. The kinds of objects we take as basic.

    - Certain things called types, or higher groupoids, rather than sets, are the primitive objects.
    - Sets, also called 0-groupoids, are particular kinds of types.
    - So we have more general objects as a starting point.
    - E.g. the type `ℕ` of natural numbers is a set, and this is a theorem, not a definition.
    - E.g. the type of monoids is not a set, but instead a `1`-groupoid, automatically.
    - E.g. the type of categories is a `2`-groupoid, again automatically.

 2. The treatment of logic.

    - Mathematical statements are interpreted as types rather than truth values.
    - Truth values are particular kinds of types, called `-1`-groupoids, with at most one element.
    - Logical operations are particular cases of mathematical operations on types.
    - The mathematics comes first, with logic as a derived concept.
    - E.g. when we say "and", we are taking the cartesian product of two types, which may or may not be truth values.

 3. The treatment of equality.

    - The value of an equality `x ≡ y` is a type, called the *identity type*, which is not necessarily a truth value.
    - It collects the ways in which the mathematical objects `x` and `y` are identified.
    - E.g. it is a truth value for elements of `ℕ`, as there is at most one way for two natural numbers to be equal.
    - E.g. for the [type of monoids](HoTT-UF-Agda.html#magmasandmonoids), it is a set, amounting to the type of monoid isomorphisms, automatically.
    - E.g. for the type of categories, it is a `1`-groupoid, amounting to the type of equivalences of categories, again automatically.

The important word in the above description of univalent foundations
is *automatic*. For example, we don't *define* equality of monoids to
be isomorphism. Instead, we define the collection of monoids as the
large type of small types that are sets, equipped with a binary
multiplication operation and a unit satisfying associativity of
multiplication and neutrality of the unit in the usual way, and then
we *prove* that the native notion of equality that comes with
univalent type theory (inherited from Martin-Löf type theory) happens
to coincide with monoid isomorphism. Largeness and smallness are taken
as relative concepts, with type *universes* incorporated in the theory
to account for this distinction.

Voevodsky's way to achive this is to start with a Martin-Löf type
theory (MLTT), including identity types and type universes, and
postulate a single axiom, named *univalence*. This axiom stipulates a
[canonical](http://mathworld.wolfram.com/Canonical.html) bijection
between *type equivalences* (in a suitable sense defined by Voevodsky
in type theory) and *type identifications* (in the original sense of
Martin-Löf's identity type). Voevodsky's notion of type equivalence,
formulated in MLTT, is a refinement of the notion of isomorphism,
which works uniformly for all higher groupoids, i.e. types.

In particular, Voevodsky didn't design a new type theory, but instead
gave an axiom for an existing type theory (or any of a family of
possible type theories, to be more precise).

The main *technical* contributions in type theory by Voevodsky are:

<ol start="4">
   <li>The definition of type levels in MLTT, classifying them as n-groupoids including the possibility n=∞.</li>
   <li>The (simple and elegant) definition of type equivalence that works uniformly for all type levels in MLTT.</li>
   <li> The formulation of the univalence axiom in MLTT.</li>
</ol>

Univalent mathematics begins within MLTT with (4) and (5) before we
postulate univalence. In fact, as the reader will see, we will do a
fair amount of univalent mathematics before we formulate or assume the
univalence axiom.

All of (4)-(6) crucially rely on Martin-Löf's identity
type. [Initially](https://faculty.math.illinois.edu/~dan/Papers/ITP-talk.pdf), Voevodsky thought that a new concept would be needed
in the type theory to achieve (4)-(6) and hence (1) and (3) above. But
he eventually discovered that Martin-Löf's identity type is precisely
what he needed.

It may be considered somewhat miraculous that the addition of the
univalence axiom alone to MLTT can achieve (1) and (3). Martin-Löf
type theory was designed to achieve (2), and, regarding (1), types
were imagined/conceived as sets (and even named *sets* in some of the
original expositions by Martin-Löf), and, regarding (3), the identity
type was imagined/conceived as having at most one element, even if
MLTT cannot prove or disprove this statement, as was eventually
shown by
[Hofmann](https://www.tcs.ifi.lmu.de/mitarbeiter/martin-hofmann) and
[Streicher](https://en.wikipedia.org/wiki/Thomas_Streicher) with their
[groupoid model of types](https://ieeexplore.ieee.org/document/316071)
in the early 1990's.

Another important aspect of univalent mathematics is the presence of
explicit mechanisms for distinguishing

<ol start="7">
 <li>property (e.g. an unspecified thing exists),</li>
 <li>data or structure (e.g. a designated thing exists or is given),</li>
</ol>

which are common place in current mathematical practice
(e.g. cartesian closedness of a category is a property in some sense
(up to isomorphism), whereas monoidal closedness is given structure).

In summary, univalent mathematics is characterized by (1)-(8) and not
by the univalence axiom alone. In fact, 3/4 of theses notes begin
*without* the univalence axiom (as measured by the number of lines in
the source code for these lecture notes until we formulate the
univalence axiom and start to use it).

Lastly, univalent type theories don't assume the axiom of choice or
the principle of excluded middle, and so in some sense they are
constructive by default. But we emphasize that these two axioms are
consistent and hence can be safely used as assumptions. However,
virtually all theorems of univalent mathematics, e.g. in
[UniMath](https://github.com/UniMath/UniMath/blob/master/README.md),
have been proved without assuming them, with natural mathematical
arguments. The formulations of theses principles in univalent
mathematics differ from their traditional formulations in MLTT, and
hence we sometimes refer to them as the *univalent* principle of
excluded middle and the *univalent* axiom of choice.

In these notes we will explore the above ideas, using Agda to write
MLTT definitions, constructions, theorems and proofs, with
univalence as an explicit assumption each time it is needed. We will
have a further assumption, the existence of certain subsingleton (or
propositional, or truth-value) truncations in order to be able to deal
with the distinction between property and data, and in particular with
the distinction between designated and unspecified existence (for
example to be able to define the notions of image of a function and of
surjective function). However, we will not assume them globally, so
that the students can see clearly when univalence or truncation are or
are not needed. In fact, the foundational definitions, constructions,
theorems and proofs of univalent mathematics don't require univalence
or propositional truncation, and so can be developed in a version of
the original Martin-Löf type theories, and this is what happens in
these notes, and what Voevodsky did in his brilliant [original
development in the computer system
Coq](https://github.com/UniMath/Foundations). Our use of Agda, rather
than Coq, is a personal matter of taste only, and the students are
encouraged to learn Coq, too.

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)
#### <a id="homotopytypetheory"></a> Homotopy type theory

Univalent type theory is often called *homotopy type theory*.  Here we
are following Voevodsky, who coined the phrases *univalent
foundations* and *univalent mathematics*.
We regard the terminology *homotopy type theory* as probably more
appropriate for referring to the *synthetic* development of homotopy
theory within univalent mathematics, for which we refer the reader to
the [HoTT book](https://homotopytypetheory.org/book/).

However, the terminology *homotopy type theory* is also used as a
synonym for univalent type theory, not only because univalent type
theory has a model in homotopy types (as defined in homotopy theory),
but also because, without considering models, types do behave like
homotopy types, automatically. We will not discuss how to do homotopy
theory using univalent type theory in these notes. We refer the reader
to the HoTT book as a starting point.

A common compromise is to refer to the subject as [HoTT/UF](https://cas.oslo.no/hott-uf/).

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)
#### <a id="generalreferences"></a> General references

   - [Papers](https://github.com/michaelt/martin-lof) by [Martin-Löf](https://en.wikipedia.org/wiki/Per_Martin-L%C3%B6f).
   - Homotopy type theory website [references](https://homotopytypetheory.org/references/).
   - [HoTT book](https://homotopytypetheory.org/book/).
   - `ncatlab` [references](https://ncatlab.org/nlab/show/homotopy+type+theory#References).

It particular, it is recommended to read the concluding notes for each
chapter in the HoTT book for discussion of original sources. Moreover,
the whole HoTT book is a recommended complementary reading for this
course.

And, after the reader has gained enough experience:

   - Voevodsky's original [foundations of univalent mathematics in Coq](https://github.com/vladimirias/Foundations).
   - [UniMath project](https://github.com/UniMath/UniMath) in [Coq](https://coq.inria.fr/).
   - [Coq HoTT library](https://github.com/HoTT/HoTT).
   - [Agda HoTT library](https://github.com/HoTT/HoTT-Agda).

Regarding the computer language Agda, we recommend the following as
starting points:

   - [Agda wiki](https://wiki.portal.chalmers.se/agda/pmwiki.php).
   - [Dependent types at work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf) by Ana Bove and Peter Dybjer.
   - [Agda reference manual](https://agda.readthedocs.io/en/latest/getting-started/index.html).
   - [Agda further references](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation).
   - [Cubical Agda blog post](https://homotopytypetheory.org/2018/12/06/cubical-agda/).
   - [Cubical Agda documentation](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical).

Regarding the genesis of the subject:

   - [A very short note on homotopy λ-calculus](http://math.ucr.edu/home/baez/Voevodsky_note.ps).
   - [Notes on homotopy λ-calculus](https://github.com/vladimirias/2006_03_Homotopy_lambda_calculus/blob/master/homotopy_lambda_calculus_Mar_5_2006.pdf).

An important foundational reference, by Steve Awodey and Michael A. Warren, is

   - [Homotopy theoretic models of identity types](https://arxiv.org/abs/0709.0248).

Additional expository material:

   - [An introduction to univalent foundations for mathematicians](https://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01616-9/), a paper at the [Bulletin of the
AMS](https://www.ams.org/publications/journals/journalsframework/bull)
by [Dan Grayson](https://faculty.math.illinois.edu/~dan/).
   - [Voevodsky's Memorial talk](https://faculty.math.illinois.edu/~dan/Talks/Voevodsky-memorial-talk.pdf)
by [Dan Grayson](https://faculty.math.illinois.edu/~dan/).
   - [Univalent foundations - an introduction](https://benediktahrens.net/talks/6WFT.pdf) by Benedikt Ahrens.
   - [Introduction to Homotopy Type Theory](https://github.com/EgbertRijke/HoTT-Intro) by Egbert Rijke.
   - [A course on homotopy (type) theory](http://math.andrej.com/2019/05/08/a-course-on-homotopy-type-theory/) by Andrej Bauer and Jaka Smrekar.
  - [15-819 Homotopy Type Theory](https://www.cs.cmu.edu/~rwh/courses/hott/) by Bob Harper.
  - [Homotopy type theory: the logic of space](https://arxiv.org/abs/1703.03007) by Mike Shulman.
  - [Logic in univalent type theory](https://www.newton.ac.uk/seminar/20170711100011001) by Martin Escardo.

More references as clickable links are given in the course of the notes.

We also have an [Agda development](http://www.cs.bham.ac.uk/~mhe/agda-new/)
of [univalent
foundations](http://www.cs.bham.ac.uk/~mhe/agda-new/UF.html) which is
applied to work on [injective
types](http://www.cs.bham.ac.uk/~mhe/agda-new/InjectiveTypes-article.html),
[compact (or searchable)
types](http://www.cs.bham.ac.uk/~mhe/agda-new/Compactness.html),
[compact
ordinals](http://www.cs.bham.ac.uk/~mhe/agda-new/Ordinals.html) and
[more](http://www.cs.bham.ac.uk/~mhe/agda-new/SafeModulesIndex.html).

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)
### <a id="plan"></a> Choice of material

This is intended as an introductory graduate course. We include what
we regard as the essence of univalent foundations and univalent
mathematics, but we are certainly omitting important material that is
needed to do univalent mathematics in practice, and the readers who wish
to practice univalent mathematics should consult the above references.

### <a id="contents"></a> Table of contents

  1. [Front matter](HoTT-UF-Agda.html#lecturenotes)
     1. [First page](HoTT-UF-Agda.html#lecturenotes)
     1. [Introduction](HoTT-UF-Agda.html#introduction)
     1. [Homotopy type theory](HoTT-UF-Agda.html#homotopytypetheory)
     1. [General references](HoTT-UF-Agda.html#generalreferences)
     1. [Choice of material](HoTT-UF-Agda.html#plan)
  1. [MLTT in Agda](HoTT-UF-Agda.html#mlttinagda)
     1. [A spartan Martin-Löf type theory (MLTT)](HoTT-UF-Agda.html#spartanmltt)
     1. [What is Agda?](HoTT-UF-Agda.html#whatisagda)
     1. [Getting started with Agda](HoTT-UF-Agda.html#gettingstartedagda)
     1. [Universes `𝓤,𝓥,𝓦`](HoTT-UF-Agda.html#universes)
     1. [The one-element type `𝟙`](HoTT-UF-Agda.html#onepointtype)
     1. [The empty type `𝟘`](HoTT-UF-Agda.html#emptytype)
     1. [The type `ℕ` of natural numbers](HoTT-UF-Agda.html#naturalnumbers)
     1. [The binary sum type constructor `_+_`](HoTT-UF-Agda.html#binarysum)
     1. [`Σ` types](HoTT-UF-Agda.html#sigmatypes)
     1. [`Π` types](HoTT-UF-Agda.html#pitypes)
     1. [The identity type former `Id`, also written `_≡_`](HoTT-UF-Agda.html#identitytype)
     1. [Basic constructions with the identity type](HoTT-UF-Agda.html#basicidentity)
     1. [Reasoning with negation](HoTT-UF-Agda.html#negation)
     1. [Example: formulation of the twin-prime conjecture](HoTT-UF-Agda.html#twinprime)
     1. [Remaining Peano axioms and basic arithmetic](HoTT-UF-Agda.html#basicarithmetic)
  1. [Univalent Mathematics in Agda](HoTT-UF-Agda.html#uminagda)
     1. [Our univalent type theory](HoTT-UF-Agda.html#axiomaticutt)
     1. [Subsingletons (or propositions or truth values) and sets](HoTT-UF-Agda.html#subsingletonsandsets)
     1. [The types of magmas and monoids](HoTT-UF-Agda.html#magmasandmonoids)
     1. [The identity type in univalent mathematics](HoTT-UF-Agda.html#identitytypeuf)
     1. [Identifications that depend on identifications](HoTT-UF-Agda.html#dependentequality)
     1. [Equality in Σ types](HoTT-UF-Agda.html#sigmaequality)
     1. [Voevodsky's notion of hlevel](HoTT-UF-Agda.html#hlevel)
     1. [The univalent principle of excluded middle](HoTT-UF-Agda.html#em)
     1. [Hedberg's Theorem](HoTT-UF-Agda.html#hedberg)
     1. [A characterization of sets](HoTT-UF-Agda.html#setscharacterization)
     1. [Subsingletons are sets](HoTT-UF-Agda.html#subsingletonsaresets)
     1. [The types of hlevel 1 are the subsingletons](HoTT-UF-Agda.html#hlevel1subsingleton)
     1. [The types of hlevel 2 are the sets](HoTT-UF-Agda.html#hlevel2set)
     1. [The hlevels are upper closed](HoTT-UF-Agda.html#hlevelsupper)
     1. [ℕ is a set](HoTT-UF-Agda.html#naturalsset)
     1. [Retracts](HoTT-UF-Agda.html#retracts)
     1. [Voevodsky' notion of type equivalence](HoTT-UF-Agda.html#fibersandequivalences)
     1. [Voevodsky's univalence axiom](HoTT-UF-Agda.html#univalence)
     1. [Example of a type that is not a set under univalence](HoTT-UF-Agda.html#notsets)
     1. [Exercises](HoTT-UF-Agda.html#lefttothereader)
     1. [Solutions](HoTT-UF-Agda.html#solutions)
     1. [A characterization of univalence](HoTT-UF-Agda.html#unicharac)
     1. [Equivalence induction](HoTT-UF-Agda.html#equivalenceinduction)
     1. [Half adjoint equivalences](HoTT-UF-Agda.html#haes)
     1. [Function extensionality from univalence](HoTT-UF-Agda.html#funextfromua)
     1. [Variations of function extensionality and their logical equivalence](HoTT-UF-Agda.html#hfunext)
     1. [Universes are map classifiers](HoTT-UF-Agda.html#typeclassifier)
     1. [The univalence axiom is a (sub)singleton type](HoTT-UF-Agda.html#univalencesubsingleton)
     1. [`hfunext` and `vvfunext` are subsingletons](HoTT-UF-Agda.html#hfunextsubsingleton)
     1. [More consequences of function extensionality](HoTT-UF-Agda.html#morefunextuses)
     1. [Propositional extensionality](HoTT-UF-Agda.html#propositionalextensionality)
     1. [Some constructions with types of equivalences](HoTT-UF-Agda.html#equivconstructions)
     1. [Type embeddings](HoTT-UF-Agda.html#embeddings)
     1. [The Yoneda Lemma for types](HoTT-UF-Agda.html#yoneda)
     1. [Universe lifting](HoTT-UF-Agda.html#universelifting)
     1. [The subtype classifier and other classifiers](HoTT-UF-Agda.html#subtypeclassifier)
     1. [Magma equivalences](HoTT-UF-Agda.html#magmaequivalences)
     1. [Structure identity principle](HoTT-UF-Agda.html#sip)
     1. [Subsingleton truncation](HoTT-UF-Agda.html#truncation)
     1. [The univalent axiom of choice](HoTT-UF-Agda.html#choice)
  1. [Appendix](HoTT-UF-Agda.html#appendix)
     1. [Operator fixities and precedences](HoTT-UF-Agda.html#infixop)
     1. [Additional exercises](HoTT-UF-Agda.html#moreexercises)
     1. [Solutions](HoTT-UF-Agda.html#mlttexercisessol)
     1. [Agda files automatically extracted from these notes](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/tree/master/agda)
     1. [The sources for these notes](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes)
     1. [License](LICENSE)

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="mlttinagda"></a> MLTT in Agda

### <a id="whatisagda"></a> What is Agda?

There are [two views](https://agda.readthedocs.io/en/latest/getting-started/what-is-agda.html):

 1. Agda is a dependently-typed functional programming language.

 2. Agda is a language for defining mathematical notions (e.g. group
    or topological space), formulating constructions to be performed
    (e.g. a type of real numbers, a group structure on the integers, a
    topology on the reals), formulating theorems (e.g. a certain
    construction is indeed a group structure, there are infinitely
    many primes), and proving theorems (e.g. the infinitude of the
    collection of primes with Euclid's argument).

This doesn't mean that Agda has two sets of features, one for (1) and
the other for (2). The same set of features account simultaneously for
(1) and (2). Programs are mathematical constructions that happen not
to use non-constructive principles such as excluded middle.

In these notes we study a minimal univalent type theory and do
mathematics with it using a minimal subset of the computer language Agda
as a vehicle.

Agda allows one to construct proofs interactively, but we will not
discuss how to do this in these notes. Agda is not an automatic
theorem prover. We have to come up with our own proofs, which Agda
checks for correctness. We do get some form of interactive help to
input our proofs and render them as formal objects.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="spartanmltt"></a> A spartan Martin-Löf type theory (MLTT)

Before embarking into a full definition of our Martin-Löf type
theory in Agda, we summarize the particular Martin-Löf type
theory that we will consider, by naming the concepts that we will
include. We will have:

   * An empty type [`𝟘`](HoTT-UF-Agda.html#emptytype).

   * A one-element type [`𝟙`](HoTT-UF-Agda.html#onepointtype).

   * A type of [`ℕ`](HoTT-UF-Agda.html#naturalnumbers) natural numbers.

   * Type formers [`+`](HoTT-UF-Agda.html#binarysum) (binary sum),
     [`Π`](HoTT-UF-Agda.html#pitypes) (product),
     [`Σ`](HoTT-UF-Agda.html#sigmatypes) (sum),
     [`Id`](HoTT-UF-Agda.html#identitytype) (identity type).

   * [Universes](HoTT-UF-Agda.html#universes) (types of types), ranged
     over by `𝓤,𝓥,𝓦`.

This is enough to do number theory, analysis, group theory, topology, category theory and more.

spartan
  /ˈspɑːt(ə)n/
  adjective:

      showing or characterized by austerity or a lack of comfort or
      luxury.

We will also be rather spartan with the subset of Agda that we choose
to discuss. Many things we do here can be written in more concise ways
using more advanced features. Here we introduce a minimal
subset of Agda where everything in our spartan MLTT can be expressed.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="gettingstartedagda"></a> Getting started with Agda

We don't use any Agda library. For pedagogical purposes, we start from
scratch, and here are our first two lines of code:

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where
\end{code}

 * The option [`--without-K`](https://agda.readthedocs.io/en/latest/language/without-k.html) disables [Streicher's `K` axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29), which we don't
   want for univalent mathematics.

 * The option [`--exact-split`](https://agda.readthedocs.io/en/latest/language/function-definitions.html#case-trees) makes Agda to only accept definitions
   with the equality sign "`=`" that behave like so-called
   *judgmental* or *definitional* equalities.

 * The option [`--safe`](https://agda.readthedocs.io/en/latest/language/safe-agda.html#safe-agda) disables features that may make Agda
   inconsistent,
   such as `--type-in-type`, postulates and more.

 * Every Agda file is a
  [module](https://agda.readthedocs.io/en/latest/language/module-system.html).
  These lecture notes are a set of Agda files, which are converted to
  html by Agda after it successfully checks the mathematical
  development for correctness.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="universes"></a> Universes

A universe `𝓤` is a type of types.

 * One use of universes is to define families of types indexed by a
   type `X` as functions `X → 𝓤`.

 * Such a function is [sometimes](HoTT-UF-Agda.html#twinprime) seen as a property of elements of `X`.

 * Another use of universes, as we shall see, is to define types of
   mathematical structures, such as
   [monoids](HoTT-UF-Agda.html#magmasandmonoids), groups, topological
   spaces, categories etc.

Sometimes we need more than one universe. For example, the type of
groups in a universe lives in a bigger universe, and given a category
in one universe, its presheaf category also lives in a larger universe.

We will work with a tower of type universes

   > `𝓤₀, 𝓤₁, 𝓤₂, 𝓤₃, ...`

These are actually universe names (also called levels, not to be confused with [hlevels](HoTT-UF-Agda.html#hlevel)). We reference
the universes themselves by a deliberately almost-invisible
superscript dot. For example, we will have

   > `𝟙 : 𝓤₀ ̇`

where `𝟙` is the one-point type to be defined shortly. We will sometimes
omit this superscript in our discussions, but are forced to write it
in Agda code. We have that the universe `𝓤₀` is a type in the universe
`𝓤₁`, which is a type in the universe 𝓤₂ and so on.

   > `𝓤₀ ̇` &nbsp;&nbsp;    `: 𝓤₁ ̇`

   > `𝓤₁ ̇` &nbsp;&nbsp;    `: 𝓤₂ ̇`

   > `𝓤₂ ̇` &nbsp;&nbsp;    `: 𝓤₃ ̇`

   > `       ⋮ `

The assumption that `𝓤₀ : 𝓤₀` or that any universe is in itself or a
smaller universe [gives rise to a
contradiction](https://link.springer.com/article/10.1007/BF01995104),
similar to [Russell's
Paradox](https://plato.stanford.edu/entries/russell-paradox/).

Given a universe `𝓤`, we denote by

   > `𝓤 ⁺`

its successor universe. For example, if `𝓤` is `𝓤₀` then `𝓤 ⁺` is
`𝓤₁`. The least upper bound of two universes `𝓤` and `𝓥` is written

   > `𝓤 ⊔ 𝓥`.

For example, if `𝓤` is `𝓤₀` and `𝓥` is `𝓤₁`, then `𝓤 ⊔ 𝓥` is `𝓤₁`.

We now bring our notation for universes by importing our Agda file
[`Universes`](Universes.html). The Agda keyword
[`open`](https://agda.readthedocs.io/en/latest/language/module-system.html)
asks to make all definitions in the file `Universe` visible in our
file here. The Agda code in these notes has syntax highlighting and
links, so that we can navigate to the definition of a name or symbol by clicking at it.
\begin{code}
open import Universes public
\end{code}

The keyword `public` makes the contents of the file `Universes`
available to importers of our module `HoTT-UF-Agda`.

We will refer to universes by letters `𝓤,𝓥,𝓦,𝓣`:

\begin{code}
variable
 𝓤 𝓥 𝓦 𝓣 : Universe
\end{code}

In some type theories, the universes are cumulative "on the nose", in
the sense that from `X : 𝓤` we derive that `X : 𝓤 ⊔ 𝓥`. We will
[instead](HoTT-UF-Agda.html#universelifting) have an embedding `𝓤 → 𝓤 ⊔
𝓥` of universes into larger universes.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="onepointtype"></a> The one-element type `𝟙`

We place it in the first universe, and we name its unique element
"`⋆`". We use the `data` declaration in Agda to introduce it:

\begin{code}
data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙
\end{code}

It is important that the point `⋆` lives in the type `𝟙` and in no other
type. There isn't dual citizenship in our type theory. When we create
a type, we also create freshly new elements for it, in this case
"`⋆`". (However, Agda has a limited form of overloading, which allows
us to sometimes use the same name for different things.)

Next we want to give a mechanism to prove that all points of the
type `𝟙` satisfy a given property `A`.

  * The property is a function `A : 𝟙 → 𝓤` for some universe `𝓤`.

  * The type `A(x)`, which we will write simply `A x`, doesn't need to
    be a [truth value](HoTT-UF-Agda.html#subsingletonsandsets).  It can be
    any type. We will meet examples shortly.

  * Mathematical statements are types, such as

    > `Π (A : 𝟙 → 𝓤), A ⋆ → Π (x : 𝟙), A x`.

  * We read this in natural language as "for any given property `A` of
    elements of the type `𝟙`, if `A ⋆` holds, then it follows that `A
    x` holds for all `x : 𝟙`".


  * In Agda the above `Π` type is written as

    > `(A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x`.

    This is the type of functions with three arguments `A : 𝟙 → 𝓤 ̇` &nbsp;
    and `a : A ⋆` and `x : 𝟙`, with values in the type `A x`.

  * A proof of a mathematical statement rendered as a type is a
    construction of an element of the type.  In our example, we have
    to construct a function, which we will name `𝟙-induction`.

We do this as follows in Agda, where we first declare the type of the
function `𝟙-induction` with "`:`" and then define the function by an
equation:

\begin{code}
𝟙-induction : (A : 𝟙 → 𝓤 ̇ )
            → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a
\end{code}

Notice that we supply `A` and `a` as arbitrary arguments, but instead of
an arbitrary `x : 𝟙` we have written "`⋆`". Agda accepts this because it
knows from the definition of `𝟙` that "`⋆`" is the only element of the
type `𝟙`. This mechanism is called *pattern matching*.

A particular case of `𝟙-induction` occurs when the family `A` is constant
with value `B`, which can be written variously as `A = λ (x : 𝟙) → B`,
or `A = λ x → B` if we want Agda to figure out the type of `x` by itself,
or `A = λ _ → B` if we don't want to name the argument of `A` because it
is not used. In usual mathematical practice, such a [lambda expression](https://plato.stanford.edu/entries/lambda-calculus/) is [often
written](https://en.wikipedia.org/wiki/Function_(mathematics)#Arrow_notation) `x ↦ B` (`x` is mapped to `B`) and so `A = (x ↦ B)`.
Given a type `B` and a point `b : B`, we construct the function `𝟙 → B`
that maps any given `x : 𝟙` to `b`.

\begin{code}
𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x
\end{code}

Not all types have to be seen as mathematical statements (for example
the type `ℕ` of natural numbers defined below). But the above definition
has a dual interpretation as a mathematical function, and as the
statement "`B` implies (*true* implies `B`)" where `𝟙` is the type encoding
the truth value *true*.

The unique function to `𝟙` will be named `!𝟙`. We define two versions
to illustrate [implicit
arguments](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html),
which correspond in mathematics to "subscripts that are omitted when
the reader can safely infer them", as for example for the identity
function of a set or the identity arrow of an object of a category.

\begin{code}
!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆
\end{code}

This means that when we write `!𝟙 x` we have to recover the (uniquely
determined) missing type `X` with `x : X` "from the context". When
Agda can't figure it out, we need to supply it and write `!𝟙 {𝓤} {X}
x`. This is because `𝓤` is also an implicit argument (all things
declared with the Agda keyword *variable* [as above](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html#universes) are implicit
arguments). There are
[other](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html),
non-positional, ways to indicate `X` without having to indicate `𝓤`
too. Occasionally, people define variants of a function with different
choices of "implicitness", as above.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="emptytype"></a> The empty type `𝟘`

It is defined like `𝟙`, except that no elements are listed for it:

\begin{code}
data 𝟘 : 𝓤₀ ̇  where
\end{code}

That's the complete definition. This has a dual interpretation,
mathematically as the empty set (we can actually prove that this type
is a set, once we know the definition of set), and logically as the
truth value *false*. To prove that a property of elements of the empty
type holds for all elements of the empty type, we have to do nothing.

\begin{code}
𝟘-induction : (A : 𝟘 → 𝓤 ̇ )
            → (x : 𝟘) → A x
𝟘-induction A ()
\end{code}

When we write the pattern `()`, Agda checks if there is any case we
missed. If there is none, our definition is accepted.  The expression
`()` corresponds to the mathematical phrase [vacuously
true](https://en.wikipedia.org/wiki/Vacuous_truth). The unique
function from `𝟘` to any type is a particular case of `𝟘-induction`.

\begin{code}
𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a
\end{code}

We will use the following categorical notation for `𝟘-recursion`:

\begin{code}
!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion
\end{code}

We give the two names `is-empty` and `¬` to the same function now:

\begin{code}
is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘
\end{code}

This says that a type is empty precisely when we have a function to
the empty type. Assuming [univalence](HoTT-UF-Agda.html#univalence),
once we have defined the identity type former
[`_≡_`](HoTT-UF-Agda.html#identitytype), we will be able to prove that
`(is-empty X) ≡ (X ≃ 𝟘)`, where `X ≃ 𝟘` is the type of bijections, or
[equivalences](HoTT-UF-Agda.html#fibersandequivalences), from `X` to
`𝟘`. We will also be able to prove things like `(2 + 2 ≡ 5) ≡ 𝟘` and
`(2 + 2 ≡ 4) ≡ 𝟙`.

This is for *numbers*. If we define *types* `𝟚 = 𝟙 + 𝟙` and `𝟜 = 𝟚 +
𝟚` with two and four elements respectively, where we are anticipating
the definition of [`_+_`](HoTT-UF-Agda.html#binarysum) for types, then we
will instead have that `𝟚 + 𝟚 ≡ 𝟜` is a type with `4!` elements, which
is [number of permutations](https://en.wikipedia.org/wiki/Factorial)
of a set with four elements, rather than a truth value `𝟘` or `𝟙`, as
a consequence of the univalence axiom. That is, we will have `(𝟚 + 𝟚 ≡
𝟜) ≃ (𝟜 + 𝟜 + 𝟜 + 𝟜 + 𝟜 + 𝟜)`, so that the type identity `𝟚 + 𝟚 ≡ 𝟜`
holds in [many more ways](https://arxiv.org/abs/math/9802029) than the
numerical equation `2 + 2 ≡ 4`.

The above is possible only because universes are genuine types and
hence their elements (that is, types) have identity types themselves,
so that writing `X ≡ Y` for types `X` and `Y` (inhabiting the same
universe) is allowed.

When we view `𝟘` as *false*, we can read the definition of
the *negation* `¬ X` as saying that "`X` implies *false*". With univalence
we will be able to show that "(*false* → *false*) `≡` *true*", which amounts
to `(𝟘 → 𝟘) ≡ 𝟙`, which in turn says that there is precisely one function
`𝟘 → 𝟘`, namely the (vacuous) identity function.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="naturalnumbers"></a> The type `ℕ` of natural numbers

The definition is similar but not quite the same as the one via
[Peano Axioms](https://en.wikipedia.org/wiki/Peano_axioms).

We stipulate an element `zero : ℕ` and a successor function `succ : ℕ → ℕ`,
and then define induction. Once we have defined the identity type former `_≡_`, we
will [*prove*](HoTT-UF-Agda.html#naturalsset) the other peano axioms.

\begin{code}
data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ
\end{code}

In general, declarations with `data` are inductive definitions. To write the number `5`, we have to write

   > `succ (succ (succ (succ (succ zero))))`

We can use the following Agda
[*built-in*](https://agda.readthedocs.io/en/latest/language/built-ins.html)
to be able to just write `5` as a shorthand:

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}

Apart from this notational effect, the above declaration doesn't play any
role in the Agda development of these lectures notes.

In the following, the type family `A` can be seen as playing the role
of a property of elements of `ℕ`, except that it doesn't need to be
necessarily
[subsingleton](HoTT-UF-Agda.html#subsingletonsandsets) valued. When it
is, the *type* of the function gives the familiar [principle of
mathematical
induction](https://en.wikipedia.org/wiki/Mathematical_induction) for
natural numbers, whereas, in general, its definition says how to
compute with induction.

\begin{code}
ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)
\end{code}

The definition of `ℕ-induction` is itself by induction. It says that given a point `a₀ : A 0` and a function `f : (n : ℕ) → A n → A (succ n)`, in order to calculate an element of `A n` for a given `n : ℕ`, we just calculate `h n`, that is,

   > `f n (f (n-1) (f (n-2) (... (f 0 a₀)...)))`.

So the principle of induction is a construction that given a *base
case* `a₀ : A 0`, an *induction step* `f : (n : ℕ) → A n → A (succ n)` and a number `n`, says how to get
an element of the type `A n` by [primitive
recursion](https://www.encyclopediaofmath.org/index.php/Primitive_recursion).

Notice also that `ℕ-induction` is the dependently typed version of
primitive recursion, where the non-dependently typed version is

\begin{code}
ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)
\end{code}

The following special case occurs often (and is related to the fact that `ℕ` is the [initial algebra](https://en.wikipedia.org/wiki/Initial_algebra) of the functor `𝟙 + (-)`):

\begin{code}
ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)
\end{code}

Agda checks that any recursive definition as above is well founded,
with recursive invocations with structurally smaller arguments
only. If it isn't, the definition is not accepted.

In official Martin-Löf type theories, we have to use the `ℕ-induction`
functional to define everything else with the natural numbers. But Agda
allows us to define functions by structural recursion, like we defined
`ℕ-induction`.


We now define addition and multiplication for the sake of illustration.
We first do it in Peano style. We will create a local [`module`](https://agda.readthedocs.io/en/latest/language/module-system.html#) so that the
definitions are not globally visible, as we want to have the symbols
`+` and `×` free for type operations of MLTT to be defined soon. The
things in the module are indented and are visible outside the module
only if we [`open`](https://agda.readthedocs.io/en/latest/language/module-system.html#) the module or if we write them as
e.g. `Arithmetic._+_` in the following example.

\begin{code}
module Arithmetic where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 10 _+_
  infixl 11 _×_
\end{code}

The above "fixity" declarations allow us to indicate the precedences
(multiplication has higher precedence than addition) and their
associativity (here we take left-associativity as the convention, so that
e.g. `x+y+z` parses as `(x+y)+z`).

Equivalent definitions use `ℕ-induction` on the second argument `y`, via
`ℕ-iteration`:

\begin{code}
module Arithmetic' where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 0 _+_
  infixl 1 _×_
\end{code}

Here the expression "`x +_`" stands for the function `ℕ → ℕ` that adds
`x` to its argument. So to multiply `x` by `y`, we apply `y` times the
function "`x +_`" to `0`.

As another example, we define the less-than-or-equal relation by
nested induction, on the first argument and then the second, but we
use pattern
matching for the sake of readability.

*Exercise.* Write it using `ℕ-induction`, recursion or iteration, as
appropriate.

\begin{code}
module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x
\end{code}

*Exercise.* After learning [`Σ`](HoTT-UF-Agda.html#sigmatypes)
 and [`_≡_`](HoTT-UF-Agda.html#identitytype) explained below, prove that

   > `x ≤ y` if and only if `Σ \(z : ℕ) → x + z ≡ y`.

Later, after learning
[univalence](HoTT-UF-Agda.html#univalence) prove that in this case
[this implies](HoTT-UF-Agda.html#mlttexercisessol)

   > `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`.

That [bi-implication can be turned into
equality](HoTT-UF-Agda.html#univalence-gives-propext) only holds for
types that are subsingletons.

If we are doing applied mathematics and want to actually compute, we
can define a type for binary notation for the sake of efficiency, and
of course people have done [that](http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html).
Here we are not concerned with
efficiency but only with understanding how to codify mathematics in
(univalent) type theory and in Agda.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="binarysum"></a> The binary sum type constructor `_+_`

We now define the [disjoint](HoTT-UF-Agda.html#inl-inr-disjoint-images) sum of two types `X` and `Y`. The elements of
the type

   > `X + Y`

are stipulated to be of the forms

   > `inl x` and `inr y`

with `x : X` and `y : Y`. If `X : 𝓤` and `Y : 𝓥`, we stipulate that
`X + Y : 𝓤 ⊔ 𝓥 `, where

   > `𝓤 ⊔ 𝓥 `

is the [least upper bound](HoTT-UF-Agda.html#universes) of the two universes `𝓤` and
`𝓥`.  In Agda we can define this as follows.

\begin{code}
data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y
\end{code}

To prove that a property `A` of the sum holds for all `z : X + Y`, it is enough to
prove that `A(inl x)` holds for all `x : X` and that `A(inr y)` holds for
all `y : Y`. This amounts to definition by cases:

\begin{code}
+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A(inl x))
            → ((y : Y) → A(inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y
\end{code}

When the types `A` and `B` are understood as mathematical statements,
the type `A + B` is understood as the statement "`A` or `B`", because
to prove "`A` or `B`" we have to prove one of `A` and `B`. When `A` and
`B` are simultaneously possible, we have two proofs, but sometimes we
want to deliberately ignore which one we get, when we want to get a
truth value rather than a possibly more general type, and in this case
we use the [truncation](HoTT-UF-Agda.html#truncation) `∥ A + B ∥`.

But also `_+_` is used to construct mathematical objects. For example,
we can define a two-point type:

\begin{code}
𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙
\end{code}

We can name the left and right points as follows, using patterns, so
that they can be used in pattern matching:

\begin{code}
pattern ₀ = inl ⋆
pattern ₁ = inr ⋆
\end{code}

We can define induction on 𝟚 directly by pattern matching:
\begin{code}
𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁
\end{code}

Or we can prove it by induction on `_+_` and `𝟙`:
\begin{code}
𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="sigmatypes"></a> `Σ` types

Given universes `𝓤` and `𝓥`, a type

   > `X : 𝓤`

and a type family

   > `Y : X → 𝓥 `,

we want to construct its sum, which
is a type whose elements are of the form

   > `(x , y)`

with `x : X` and `y : Y x`. This sum type will live in the [least
upper bound](HoTT-UF-Agda.html#universes)

   > `𝓤 ⊔ 𝓥`

of the universes `𝓤` and `𝓥`. We will write this sum

   > `Σ Y`,

with `X`, as well as the universes, implicit. Often Agda, and people,
can figure out what the unwritten type `X` is, from the definition of `Y`. But
sometimes there may be either lack of enough information, or of
enough concentration power by people, or of sufficiently powerful inference
algorithms in the implementation of Agda. In such cases we can write

   > `Σ λ(x : X) → Y x`,

because `Y = λ (x : X) → Y x` by a so-called η-rule. However, we will
often use the synonym `\` of `λ` for `Σ`, as if considering it as part
of the `Σ` syntax.

   > `Σ \(x : X) → Y x`.

In MLTT we would write this as `Σ (x : X), Y x` or
[similar](https://en.wikipedia.org/wiki/Summation), for example with
the indexing `x : X` written as a subscript of `Σ` or under it.


Or it may be that the name `Y` is not defined, and we work with a
nameless family defined on the fly, as in the exercise proposed above:

   > `Σ \(z : ℕ) → x + z ≡ y`,

where `Y z = (x + z ≡ y)` in this case, and where we haven't defined
the [identity type former](HoTT-UF-Agda.html#identitytype) `_≡_` yet.

We can construct the `Σ` type former as follows in Agda:

\begin{code}
record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   x : X
   y : Y x
\end{code}

This says we are defining a binary operator `_,_` to construct the
elements of this type as `x , y`. The brackets are not needed, but we
will often write them to get the more familiar notation `(x , y)`. The
definition says that an element of `Σ Y` has two `fields`, giving the
types for them.

*Remark.* Beginners may safely ignore this remark: Normally people
will call these two fields something like `pr₁` and `pr₂`, or `fst`
and `snd`, for first and second projection, rather than `x` and `y`,
and then do `open Σ public` and have the projections available as
functions automatically. But we will deliberately not do that, and
instead define the projections ourselves, because this is confusing
for beginners, no matter how mathematically or computationally versed
they may be, in particular because it will not be immediately clear
that the projections have the following types.

\begin{code}
pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y
\end{code}

To prove that `A z` holds for all `z : Σ Y`, for a given
property `A`, we just prove that we have `A(x , y)` for all `x :
X` and `y : Y x`.  This is called `Σ` induction or `Σ`
elimination, or `uncurry`, after [Haskell
Curry](https://en.wikipedia.org/wiki/Haskell_Curry).
\begin{code}
Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A(x , y))
            → (z : Σ Y) → A z
Σ-induction g (x , y) = g x y
\end{code}

This function has an inverse:

\begin{code}
curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → ((z : Σ Y) → A z)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)
\end{code}

An important particular case of the sum type is the binary cartesian
product, when the type family doesn't depend on the indexing type:

\begin{code}
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y
\end{code}

We have seen by way of examples that the function type symbol `→`
represents logical implication, and that a dependent function type
`(x : X) → A x` represents a universal quantification.

We have the following uses of `Σ`.

  * The binary cartesian product represents conjunction "and". If the
    types `A` and `B` stand for mathematical statements, then the mathematical
    statement "`A` and `B`" is codified as `A × B`. This is because to prove
    "`A` and `B`", we have to provide a pair `(a , b)` of proofs `a : A` and `b : B`.

    So notice that in type theory proofs are mathematical objects,
    rather than meta-mathematical entities like in set theory. They are
    just elements of types.

  * The more general type `Σ (x : X), A x`, if the type `X` stands
    for a mathematical object and `A` stands for a mathematical
    statement, represents *designated* existence "there is a
    designated `x : X` with `A x`".  To prove this, we have to provide
    a specific `x : X` and a proof `a : A x`, together in a pair `(x ,
    a)`.

  * Later we will discuss *unspecified* existence `∃ (x : X), A x`,
    which will be obtained by a sort of quotient of `Σ (x : X), A x`,
    written `∥ Σ (x : X), A x ∥` that identifies all the elements of
    the type `Σ (x : X), A x` in a single equivalence class, called
    its subsingleton (or truth value or propositional)
    [truncation](HoTT-UF-Agda.html#truncation).

  * Another reading of `Σ (x : X), A x` is as "the type of `x : X`
    with `A x`", similar to subset notation `{ x ∈ X | A x }` in set
    theory. But have to be careful because if there is more than one
    element in the type `A x`, then `x` is put more than once in this
    type. In such situations, if we don't want that, we have to be
    careful and either ensure that the type `A x` has at most one
    element for every `x : X`, or instead consider the truncated type
    `∥ A x ∥` and write `Σ (x : X), ∥ A x ∥`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="pitypes"></a> `Π` types

`Π` types are builtin with a different notation in Agda, as discussed
above, but we can introduce the notation `Π` for them, similar to that for `Σ`:

\begin{code}
Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x
\end{code}

Notice that the function type `X → Y` is the particular case of the `Π`
type when the family `A` is constant with value `Y`.

We take the opportunity to define the identity function (in two
versions with different implicit arguments) and function composition:

\begin{code}
id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 X = id
\end{code}

Usually the type of function composition `_∘_` is given as simply

   >  `(Y → Z) → (X → Y) → (X → Z)`.

With dependent functions, we can give it a more general type:

\begin{code}
_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)
\end{code}

Notice that this type for the composition function can be read as a mathematical
statement: If `Z y` holds for all `y : Y`, then for any given `f : X →
Y` we have that `Z (f x)` holds for all `x : X`. And the non-dependent
one is just the transitivity of implication.

The following functions are sometimes useful when we are using
implicit arguments, in order to recover them explicitly without having
to list them as given arguments:

\begin{code}
domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="identitytype"></a> The identity type former `Id`, also written `_≡_`

We now introduce the central type constructor of MLTT from the point
of view of univalent mathematics. In Agda we can define Martin-Löf's
identity type as follows:

\begin{code}
data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x
\end{code}

Intuitively, the above definition would say that the only element
of the type `Id X x x` is something called `refl x` (for
reflexivity). But, as we shall see in a moment, this intuition turns
out to be incorrect.

Notice a crucial difference with the previous definitions using `data`
or induction: In the previous cases, we defined *types*, namely `𝟘`,
`𝟙`, `ℕ`, or a *type depending on type parameters*, namely `_+_`, with `𝓤`
and `𝓥` fixed,

   > `_+_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇`

But here we are defining a *type family* indexed by the *elements* of
a given type, rather than a new type from old types. Given a type `X`
in a universe `𝓤`, we define a *function*

   > `Id X : X → X → 𝓤`

by some mysterious sort of induction. It is this that prevents us from
being able to prove that `refl x` would be the only element of the type `Id
X x x`, or that the type `Id X x y` would have at most one element no
matter what `y : X` is.

There is however, one interesting, and crucial, thing we
[can prove](HoTT-UF-Agda.html#singleton-type), namely that for any fixed `x : X`, the
type


   > `Σ \(y : Y) → Id X x y`

is always a [singleton](HoTT-UF-Agda.html#hlevel).

We will use the following alternative notation for the identity type
former `Id`, where the symbol "`_`" in the right-hand side of the
definition indicates that we ask Agda to infer which type we are
talking about (which is `X`, but this name is not available in the
scope of the *defining equation* of `_≡_`):

\begin{code}
_≡_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≡ y = Id _ x y
\end{code}

Another intuition for this type family `_≡_ : X → X → 𝓤` is that it
gives the least reflexive relation on the type `X`, as suggested by
Martin-Löf's induction principle `J` discussed below.

Whereas we can make the intuition that `x ≡ x` has precisely one
element good by *postulating* a certain [`K`
axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29) due to
Thomas Streicher, which comes with Agda by default but we have
[disabled above](HoTT-UF-Agda.html#gettingstartedagda), we cannot
*prove* that `refl x` is the only element of `x ≡ x` for an arbitrary
type `X`. This non-provability result was established by [Hofmann and
Streicher](https://ieeexplore.ieee.org/document/316071), by giving a
model of type theory in which types are interpreted as
[`1`-groupoids](https://en.wikipedia.org/wiki/Groupoid). This is in
spirit similar to the non-provability of the [parallel
postulate](https://en.wikipedia.org/wiki/Parallel_postulate) in
Euclidean geometry, which also considers models, which in turn are
interesting in their own right.

However, for the elements of *some* types, such as `ℕ`, it is
[possible to prove](HoTT-UF-Agda.html#naturalsset) that any identity
type `x ≡ y` has at most one element. Such types are called [sets in
univalent mathematics](HoTT-UF-Agda.html#subsingletonsandsets).

If instead of the axiom `K` we adopt Voevodsky's
[univalence](HoTT-UF-Agda.html#univalence) axiom, we get [specific
examples](HoTT-UF-Agda.html#notsets) of objects `x` and `y` such that
the type `x ≡ y` has multiple elements, *within* the type theory.  It
follows that the identity type `x ≡ y` is fairly under-specified in
general, in that we can't prove or disprove that it has at most one
element.

There are two opposing ways to resolve the ambiguity or
under-specification of the identity types: (1) We can consider the `K`
axiom, which postulates that all types are sets, or (2) we can
consider the univalence axiom, arriving at univalent mathematics,
which gives rise to types that are more general than sets, the
`n`-groupoids and `∞`-groupoids.  In fact, the univalence axiom will
say, in particular, that for some types `X` and elements `x y : X`, the
identity type `x ≡ y` does have more than one element.

A possible way to understand the point `refl x` of the type `x ≡ x` is
as the "generic identification" between `x` and itself, but which is
by no means necessarily the *only* identitification in univalent
foundations. It is generic in the sense that to explain what happens
with all identifications `p : x ≡ y` between any two points `x` and
`y` of a type `X`, it suffices to explain what happens with the
identification `refl x : x ≡ x` for all points `x : X`. This
is what the induction principle for identity given by Martin-Löf says,
which he called `J` (we could have called it `≡-induction`, but we
prefer to honour MLTT tradition):

\begin{code}
J : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
J X A f x x (refl x) = f x
\end{code}

This is [related](http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html) to the [Yoneda
Lemma](https://en.wikipedia.org/wiki/Yoneda_lemma) in category theory,
for readers familiar with the subject, which says that certain natural
transformations are *uniquely determined* by their *action on the
identity arrows*, even if they are *defined for all arrows*. Similarly
here, `J` is uniquely determined by its action on reflexive
identifications, but is *defined for all identifications between any
two points*, not just reflexivities.

In summary, Martin-Löf's identity type is given by the data

  * `Id`,
  * `refl`,
  * `J`,
  * the above equation for `J`.

However, we will not always use this induction principle, because we
can instead work with the instances we need by pattern matching on
`refl` (which is just what we did to define the principle itself) and
there is a [theorem by Jesper
Cockx](https://dl.acm.org/citation.cfm?id=2628139) that says that
with the Agda option `without-K`, pattern matching on `refl` can
define/prove precisely what `J` can.

*Exercise*. Define
\begin{code}
H : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
H x B b x (refl x) = b
\end{code}

Then we can define `J` from `H` as follows:

\begin{code}
J' : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
J' X A f x = H x (A x) (f x)

Js-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ≡ y)
             → J X A f x y p ≡ J' X A f x y p
Js-agreement X A f x x (refl x) = refl (f x)
\end{code}

Similarly define `H'` from `J` without using pattern matching on `refl`
and show that it coincides with `H` (possibly using pattern matching
on `refl`). This is
[harder](http://www.cse.chalmers.se/~coquand/singl.pdf).

**Notational remark.** The symbols "`=`" and "`≡`" are swapped with
  respect to the [HoTT book](https://homotopytypetheory.org/book/)
  convention for definitional/judgemental equality and type valued equality,
  and there is nothing we can do about that because "`=`" is a
  reserved Agda symbol for definitional equality. Irrespectively of
  this, it does make sense to use "`≡`" with a triple bar, if we
  understand this as indicating that there are multiple ways of
  identifying two things in general.

With this, we have concluded the rendering of our spartan MLTT in
Agda notation. Before embarking on the development of univalent
mathematics within our spartan MLTT, we pause to discuss some
basic examples of mathematics in Martin-Löf type theory.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="basicidentity"></a> Basic constructions with the identity type

*Transport along an identification.*
\begin{code}
transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl x) = 𝑖𝑑 (A x)
\end{code}

We can equivalently define transport using `J` as follows:

\begin{code}
transportJ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportJ {𝓤} {𝓥} {X} A {x} {y} = J X (λ x y _ → A x → A y) (λ x → 𝑖𝑑 (A x)) x y
\end{code}

In the same way `ℕ`-recursion can be seen as the non-dependent special
case of `ℕ`-induction, the following transport function can be seen as
the non-dependent special case of the `≡`-induction principle `H` with
some of the arguments permuted and made implicit:

\begin{code}
nondep-H : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
         → A x → (y : X) → x ≡ y → A y
nondep-H x A = H x (λ y _ → A y)

transportH : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportH A {x} {y} p a = nondep-H x A a y p
\end{code}

All the above transports coincide:

\begin{code}
transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → (transportH A p ≡ transport A p)
                     × (transportJ A p ≡ transport A p)
transports-agreement A (refl x) = refl (transport A (refl x)) ,
                                  refl (transport A (refl x))
\end{code}



The following is for use when we want to recover implicit
arguments without mentioning them.

\begin{code}
lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y
\end{code}

*Composition of identifications.*
Given two identifications `p : x ≡ y` and `q : y ≡ z`, we can compose them
to get an identification `p ∙ q : x ≡ z`. This can also be seen as
transitivity of equality. Because the type of composition doesn't
mention `p` and `q`, we can use the non-dependent version of `≡`-induction.

\begin{code}
_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p
\end{code}

Here we are considering the family `A t = (x ≡ t)`, and using the
identification `q : y ≡ z` to transport `A y` to `A z`, that is `x ≡
y` to `x ≡ z`.

*Exercise*. Define an alternative version that uses `p` to
transport. Do the two versions give equal results?

When writing `p ∙ q`, we lose information on the lhs and the rhs of the
identifications `p : x ≡ y` and `q : y ≡ z`, which makes some definitions hard to read. We now
introduce notation to be able to write e.g.

   > `x ≡⟨ p ⟩`

   > `y ≡⟨ q ⟩`

   > `z ∎`

as a synonym of the expression `p ∙ q` with some of the implicit arguments of `_∙_` made
explicit. We have one ternary [mixfix](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html) operator `_≡⟨_⟩_` and one unary
`postfix` operator `_∎`.

\begin{code}
_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x
\end{code}

*Inversion of identifications.* Given an identification, we get an
  identification in the opposite direction:

\begin{code}
_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))
\end{code}

*Application of a function to an identification*.
Given an identification `p : x ≡ x'` we get an identification
`ap f p : f x ≡ f x'` for any `f : X → Y`:

\begin{code}
ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))
\end{code}

Here the symbol "`-`", which is not to be confused with the symbol
"`_`", is a variable. We will adopt the convention in these notes of
using this variable name "`-`" to make clear which part of an
expression we are replacing with `transport`.

Notice that we have so far used the recursion principle `transport`
only. To reason about `transport`, `_∙_`, `_⁻¹` and `ap`, we [will
need](HoTT-UF-Agda.html#identitytypeuf) to use the full induction
principle `J` (or equivalently pattern matching on `refl`).

*Pointwise equality of functions*. We will work with pointwise
equality of functions, defined as follows, which, using univalence,
will be [equivalent to equality of functions](HoTT-UF-Agda.html#hfunext).

\begin{code}
_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x
\end{code}

The symbol `∀` is a built-in notation for `Π` . We could equivalently
write the *definiens* as

   > `(x : _) → f x ≡ g x`,

or, with our `Π` notation,

   > `Π \x → f x ≡ g x`,

or, with our `domain` notation

   > `(x : domain f) → f x ≡ g x`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="negation"></a> Reasoning with negation

We first introduce notation for double and triple negation to avoid
the use of brackets.

\begin{code}
¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)
\end{code}

To prove that `A → ¬¬ A`, that is, `A → ((A → 𝟘) → 𝟘)`, we start with
a hypothetical element `a : A` and a hypothetical function `u : A → 𝟘`
and the goal is to get an element of `𝟘`. All we need to do is to
apply the function `u` to `a`. This gives double-negation
introduction:

\begin{code}
dni : (A : 𝓤 ̇ ) → A → ¬¬ A
dni A a u = u a
\end{code}

Mathematically, this says that if we have a point of `A` (we say that
`A` is pointed) then `A` is nonempty. There is no general procedure to
implement the converse, that is, from a function `(A → 𝟘) → 𝟘` to get
a point of `A`. For [truth
values](HoTT-UF-Agda.html#subsingletonsandsets) `A`, we can assume
this as an axiom if we wish, because it is [equivalent to the
principle excluded middle](HoTT-UF-Agda.html#appendix). For arbitrary types `A`,
this would be a form of [global
choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice) for type
theory.  However, global choice is inconsistent with univalence [[HoTT
book](https://homotopytypetheory.org/book/), Theorem 3.2.2], because
there is no way to choose an element of every non-empty type in a way
that is invariant under automorphisms. However, the [axiom of
choice](#choice) *is* consistent with univalent type
theory, as stated in the [introduction](HoTT-UF-Agda.html#introduction).

In the proof of the following, we assume we are given hypothetical
functions `f : A → B` and `v : B → 𝟘`, and a hypothetical element `a :
A`, and our goal is to get an element of `𝟘`. But this is easy,
because `f a : B` and hence `v (f a) : 𝟘`.

\begin{code}
contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)
\end{code}

We have given a logical name to this function. Mathematically, this
says that if we have a function `A → B` and `B` is empty, then `A`
must be empty, too. The proof is by assuming that `A` would have an
inhabitant `a`, to get a contradiction, namely that `B` would have an
inhabitant, too, showing that there can't be any such inhabitant `a`
of `A` after all. See
[Bauer](http://math.andrej.com/2010/03/29/proof-of-negation-and-proof-by-contradiction/)
for a general discussion.

And from this we get that three negations imply one:
\begin{code}
tno : (A : 𝓤 ̇ ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)
\end{code}

Hence, using `dni` once again, we get that `¬¬¬ A` if and only if `¬
A`.  It is entertaining to see how Brouwer formulated and proved this
fact in his [Cambridge Lectures on
Intuitionism](https://books.google.co.uk/books/about/Brouwer_s_Cambridge_Lectures_on_Intuitio.html?id=B88L2k5KnkkC&redir_esc=y):

<blockquote>
    Theorem. Absurdity of absurdity of absurdity is equivalent to absurdity.
</blockquote>
<blockquote>
    Proof. <em>Firstly</em>, since implication of the assertion &#119910; by the
    assertion &#119909; implies implication of absurdity of &#119909; by absurdity
    of &#119910;, the implication of <em>absurdity of absurdity</em> by <em>truth</em>
    (which is an established fact) implies the implication of
    <em>absurdity of truth</em>, that is to say of <em>absurdity</em>, by <em>absurdity
    of absurdity of absurdity</em>. <em>Secondly</em>, since truth of an assertion
    implies absurdity of its absurdity, in particular truth of
    absurdity implies absurdity of absurdity of absurdity.
</blockquote>

If we define *logical equivalence* by
\begin{code}
_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)
\end{code}

then we can render Brouwer's argument in Agda as follows, where the
"established fact" is `dni`:

\begin{code}
absurdity³-is-absurdity : {A : 𝓤 ̇ } → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = contrapositive (dni A)
  secondly : ¬ A → ¬¬¬ A
  secondly = dni (¬ A)
\end{code}

But of course Brouwer, as is well known, was averse to formalism, and
hence wouldn't approve of such a sacrilege.

We now define a symbol for the negation of equality.

\begin{code}
_≢_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)
\end{code}

In the following proof, we have `u : x ≡ y → 𝟘` and need to define a
function `y ≡ x → 𝟘`. So all we need to do is to compose the function
that inverts identifications with `u`:

\begin{code}
≢-sym : {X : 𝓤 ̇ } {x y : X} → x ≢ y → y ≢ x
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)
\end{code}

To show that the type `𝟙` is not equal to the type `𝟘`, we use that
`transport id` gives `𝟙 ≡ 𝟘 → id 𝟙 → id 𝟘` where `id` is the [identity
function](HoTT-UF-Agda.html#pitypes) of the universe `𝓤₀`. More
generally, we have the following conversion of type identifications
into functions:

\begin{code}
Id-to-Fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))
\end{code}

Here the identity function is that of the universe `𝓤` where the types
`X` and `Y` live. An equivalent definition is the following, where
this time the identity function is that of the type `X`:

\begin{code}
Id-to-Fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-Fun' (refl X) = 𝑖𝑑 X

Id-to-Funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
                 → Id-to-Fun p ≡ Id-to-Fun' p
Id-to-Funs-agree (refl X) = refl (𝑖𝑑 X)
\end{code}

So if we have a hypothetical identification `p : 𝟙 ≡ 𝟘`, then we get a
function `𝟙 → 𝟘`. We apply this function to `⋆ : 𝟙` to conclude the
proof.

\begin{code}
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = Id-to-Fun p ⋆
\end{code}

To show that the elements `₁` and `₀` of the two-point type `𝟚` are
not equal, we reduce to the above case. We start with a hypothetical
identification `p : ₁ ≡ ₀`.

\begin{code}
₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p
\end{code}

*Remark.* Agda allows us to use a pattern `()` to get the following
quick proof.  However, this method of proof doesn't belong to the
realm of MLTT. Hence we will use the pattern `()` only in the above
definition of [`𝟘-induction`](HoTT-UF-Agda.html#𝟘-induction) and
nowhere else in these notes.

\begin{code}
₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()
\end{code}

Perhaps the following is sufficiently self-explanatory given the above:

\begin{code}
𝟚-has-decidable-equality : (m n : 𝟚) → (m ≡ n) + (m ≢ n)
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)
\end{code}

So we consider four cases. In the first and the last, we have equal
things and so we give an answer in the left-hand side of the sum. In
the middle two, we give an answer in the right-hand side, where we need
functions `₀ ≡ ₁ → 𝟘` and `₁ ≡ ₀ → 𝟘`, which we can take to be `≢-sym
₁-is-not-₀` and `₁-is-not-₀` respectively.

The following is more interesting. We consider the two possible cases
for `n`. The first one assumes a hypothetical function `f : ₀ ≡ ₀ →
𝟘`, from which we get `f (refl ₀) : 𝟘`, and then, using `!𝟘`, we get
an element of any type we like, which we choose to be `₀ ≡ ₁`, and we
are done. Of course, we will never be able to use the function
`not-zero-is-one` with such outrageous arguments. The other case `n = ₁`
doesn't need to use the hypothesis `f : ₁ ≡ ₀ → 𝟘`, because the
desired conclusion holds right away, as it is `₁ ≡ ₁`, which is proved
by `refl ₁`. But notice that there is nothing wrong with the
hypothesis `f : ₁ ≡ ₀ → 𝟘`. For example, we can use `not-zero-is-one`
with `n = ₀` and `f = ₁-is-not-₀`, so that the hypotheses can be
fulfilled in the second equation.

\begin{code}
not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁
\end{code}

The following generalizes `₁-is-not-₀`, both in its statement and its
proof (so we could have formulated it first and then used it to deduce
`₁-is-not-₀`):

\begin{code}
inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 q
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘
  q : 𝟙 ≡ 𝟘
  q = ap f p
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="twinprime"></a> Example: formulation of the twin-prime conjecture

We illustrate the above constructs of MLTT to formulate [this
conjecture](http://mathworld.wolfram.com/TwinPrimeConjecture.html).

\begin{code}
module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ \(p : ℕ) → (p ≥ n) × is-prime p × is-prime (p ∔ 2)
\end{code}

Thus, not only can we write down definitions, constructions, theorems
and proofs, but also conjectures. They are just definitions of
types. Likewise, the univalence axiom, [to be formulated in due course](HoTT-UF-Agda.html#univalence),
is a type.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="basicarithmetic"></a> Remaining Peano axioms and basic arithmetic

We first prove the remaining Peano axioms.

\begin{code}
positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙
  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f
\end{code}

To show that the successor function is left cancellable, we can use
the following predecessor function.

\begin{code}
pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred
\end{code}

With this we have proved all the Peano axioms.

Without assuming the principle of excluded middle, we can prove that
`ℕ` has decidable equality in the following sense:

\begin{code}
ℕ-has-decidable-equality : (x y : ℕ) → (x ≡ y) + (x ≢ y)
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : (x ≡ y) + x ≢ y → (succ x ≡ succ y) + (succ x ≢ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))
\end{code}

*Exercise.* Students should do this kind of thing at least once in
their academic life: rewrite the above proof of the decidability of
equality of `ℕ` to use the `ℕ-induction` principle instead of pattern
matching and recursion, to understand by themselves that this can be
done.

We now move to basic arithmetic, and we use a module for that.

\begin{code}
module BasicArithmetic where

  open ℕ-order
  open Arithmetic renaming (_+_ to _∔_)
\end{code}

We can show that addition is associative as follows, by induction on
`z`, where `IH` stands for "induction hypothesis":

\begin{code}
  +-assoc : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc x y zero     = (x ∔ y) ∔ 0 ≡⟨ refl _ ⟩
                         x ∔ (y ∔ 0) ∎
  +-assoc x y (succ z) = (x ∔ y) ∔ succ z   ≡⟨ refl _ ⟩
                         succ ((x ∔ y) ∔ z) ≡⟨ ap succ IH ⟩
                         succ (x ∔ (y ∔ z)) ≡⟨ refl _ ⟩
                         x ∔ (y ∔ succ z)   ∎
   where
    IH : (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
    IH = +-assoc x y z
\end{code}

Notice that the proofs `refl _` should be read as "by definition" or
"by construction". They are not necessary, because Agda knows the
definitions and silently expands them when necessary, but we are
writing them here for the sake of clarity. Elsewhere in these notes,
we do occasionally rely on silent expansions of definitions. Here is
the version with the silent expansion of definitions, for the sake of
illustration (the author of these notes can write, but not read it):

\begin{code}
  +-assoc' : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc' x y zero     = refl _
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)
\end{code}

We defined addition by induction on the second argument. Next we show
that the base case and induction step of a definition by induction on
the first argument hold (but of course not definitionally). We do this
by induction on the second argument.

\begin{code}
  +-base-on-first : (x : ℕ) → 0 ∔ x ≡ x
  +-base-on-first 0        = refl 0
  +-base-on-first (succ x) = 0 ∔ succ x   ≡⟨ refl _ ⟩
                             succ (0 ∔ x) ≡⟨ ap succ IH ⟩
                             succ x       ∎
   where
    IH : 0 ∔ x ≡ x
    IH = +-base-on-first x

  +-step-on-first : (x y : ℕ) → succ x ∔ y ≡ succ (x ∔ y)
  +-step-on-first x zero     = refl (succ x)
  +-step-on-first x (succ y) = succ x ∔ succ y   ≡⟨ refl _ ⟩
                               succ (succ x ∔ y) ≡⟨ ap succ IH ⟩
                               succ (x ∔ succ y) ∎
   where
    IH : succ x ∔ y ≡ succ (x ∔ y)
    IH = +-step-on-first x y
\end{code}

Using this, commutativity of addition can be proved by induction on the first argument.

\begin{code}
  +-comm : (x y : ℕ) → x ∔ y ≡ y ∔ x
  +-comm 0 y = 0 ∔ y ≡⟨ +-base-on-first y ⟩
               y     ≡⟨ refl _ ⟩
               y ∔ 0 ∎
  +-comm (succ x) y = succ x ∔ y  ≡⟨ +-step-on-first x y ⟩
                      succ(x ∔ y) ≡⟨ ap succ IH ⟩
                      succ(y ∔ x) ≡⟨ refl _ ⟩
                      y ∔ succ x  ∎
    where
     IH : x ∔ y ≡ y ∔ x
     IH = +-comm x y
\end{code}

We now show that addition is cancellable in its right argument, by
induction on the left argument:

\begin{code}
  +-lc : (x y z : ℕ) → x ∔ y ≡ x ∔ z → y ≡ z
  +-lc 0        y z p = y     ≡⟨ (+-base-on-first y)⁻¹ ⟩
                        0 ∔ y ≡⟨ p ⟩
                        0 ∔ z ≡⟨ +-base-on-first z ⟩
                        z     ∎
  +-lc (succ x) y z p = IH
   where
    q = succ (x ∔ y) ≡⟨ (+-step-on-first x y)⁻¹ ⟩
        succ x ∔ y   ≡⟨ p ⟩
        succ x ∔ z   ≡⟨ +-step-on-first x z ⟩
        succ (x ∔ z) ∎
    IH : y ≡ z
    IH = +-lc x y z (succ-lc q)
\end{code}

Now we solve part of an exercise given above, namely that `(x ≤ y) ⇔ Σ \(z : ℕ) → x + z ≡ y`.

First we name the alternative definition of `≤`:

\begin{code}
  _≼_ : ℕ → ℕ → 𝓤₀ ̇
  x ≼ y = Σ \(z : ℕ) → x ∔ z ≡ y
\end{code}

Next we show that the two relations `≤` and `≼` imply each other.

In both cases, we proceed by induction on both arguments.

\begin{code}
  ≤-gives-≼ : (x y : ℕ) → x ≤ y → x ≼ y
  ≤-gives-≼ 0 0               l = 0 , refl 0
  ≤-gives-≼ 0 (succ y)        l = succ y , +-base-on-first (succ y)
  ≤-gives-≼ (succ x) 0        l = !𝟘 (succ x ≼ zero) l
  ≤-gives-≼ (succ x) (succ y) l = γ
   where
    IH : x ≼ y
    IH = ≤-gives-≼ x y l
    z : ℕ
    z = pr₁ IH
    p : x ∔ z ≡ y
    p = pr₂ IH
    γ : succ x ≼ succ y
    γ = z , (succ x ∔ z   ≡⟨ +-step-on-first x z ⟩
             succ (x ∔ z) ≡⟨ ap succ p ⟩
             succ y       ∎)

  ≼-gives-≤ : (x y : ℕ) → x ≼ y → x ≤ y
  ≼-gives-≤ 0 0               (z , p) = ⋆
  ≼-gives-≤ 0 (succ y)        (z , p) = ⋆
  ≼-gives-≤ (succ x) 0        (z , p) = positive-not-zero (x ∔ z) q
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p ⟩
        zero ∎
  ≼-gives-≤ (succ x) (succ y) (z , p) = IH
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p ⟩
        succ y       ∎
    IH : x ≤ y
    IH = ≼-gives-≤ x y (z , succ-lc q)
\end{code}

[Later](HoTT-UF-Agda.html#mlttexercisessol) we will show that `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="uminagda"></a> Univalent Mathematics in Agda

### <a id="axiomaticutt"></a> Our univalent type theory

  * Spartan MLTT [as above](HoTT-UF-Agda.html#spartanmltt).
  * Univalence axiom as [below](HoTT-UF-Agda.html#univalence).
  * Subsingleton (or truth-value or propositional) truncations as [below](HoTT-UF-Agda.html#truncation).

But, as discussed above, rather than postulating univalence and truncation, we will
use them as explicit assumptions each time they are needed.

We emphasize that there are univalent type theories in which
univalence and existence of truncations are theorems, for example
cubical type theory, which has a version available in Agda, called
[cubical
Agda](https://homotopytypetheory.org/2018/12/06/cubical-agda/).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="subsingletonsandsets"></a> Subsingletons (or propositions or truth values) and sets

A type is a subsingleton (or a proposition or a truth value) if it has
at most one element, that is, any two of its elements are equal, or identified.

\begin{code}
is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = 𝟙-induction (λ x → ∀ y → x ≡ y) (𝟙-induction (λ y → ⋆ ≡ y) (refl ⋆))

𝟙-is-subsingleton' : is-subsingleton 𝟙
𝟙-is-subsingleton' ⋆ ⋆  = refl ⋆
\end{code}

The following are more logic-oriented terminologies for the notion.

\begin{code}
is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop        = is-subsingleton
is-truth-value = is-subsingleton
\end{code}

The terminology `is-subsingleton` is more mathematical and avoids the
clash with the slogan [propositions as
types](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence),
which is based on the interpretation of mathematical propositions as
arbitrary types, rather than just subsingletons.

A type is defined to be a set if there is at most one way for any two of its
elements to be equal:

\begin{code}
is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)
\end{code}

At this point, with the definition of these notions, we are entering
the realm of univalent mathematics, but not yet needing the univalence
axiom.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="magmasandmonoids"></a> The types of magmas and monoids

A [magma](https://en.wikipedia.org/wiki/Magma_(algebra)) is a *set* equipped with a binary operation subject to no laws
[[Bourbaki](https://books.google.co.uk/books?id=STS9aZ6F204C&pg=PA1&redir_esc=y#v=onepage&q&f=false)].  We can define the type of magmas in a universe `𝓤` as follows:

\begin{code}
Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X × (X → X → X)
\end{code}

The type `Magma 𝓤` collects all magmas in a universe `𝓤`, and lives in
the successor universe `𝓤 ⁺`.  Thus, this doesn't define what a magma is as
a property. It defines the type of magmas. A magma is an element of
this type, that is, a triple `(X , i , _·_)` with `X : 𝓤` and `i :
is-set X` and `_·_ : X → X → X`.

Given a magma `M = (X , i , _·_)` we denote by `⟨ M ⟩` its underlying
set `X` and by `magma-operation M` its multiplication `_·_`:

\begin{code}
⟨_⟩ : Magma 𝓤 → 𝓤 ̇
⟨ X , i , _·_ ⟩ = X

magma-is-set : (M : Magma 𝓤) → is-set ⟨ M ⟩
magma-is-set (X , i , _·_) = i

magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
magma-operation (X , i , _·_) = _·_
\end{code}

The following [syntax declaration](https://agda.readthedocs.io/en/latest/language/syntax-declarations.html)
allows us to write `x ·⟨ M ⟩ y` as an abbreviation of `magma-operation M x y`:

\begin{code}
syntax magma-operation M x y = x ·⟨ M ⟩ y
\end{code}

For some reason, Agda has this kind of definition backwards: the
*definiendum* and the *definiens* are swapped with respect to the
normal convention of writing what is defined on the left-hand side of
the equality sign. In any case, the point is that this time we need
such a mechanism because in order to be able to mention arbitrary `x`
and `y`, we first need to know their types, which is `⟨ M ⟩` and hence
`M` has to occur before `x` and `y` in the definition of
`magma-operation`. The syntax declaration circumvents this.

A function of the underlying sets of two magmas is a called a
homomorphism when it commutes with the magma operations:

\begin{code}
is-magma-hom : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
is-magma-hom M N f = (x y : ⟨ M ⟩) → f (x ·⟨ M ⟩ y) ≡ f x ·⟨ N ⟩ f y

id-is-magma-hom : (M : Magma 𝓤) → is-magma-hom M M (𝑖𝑑 ⟨ M ⟩)
id-is-magma-hom M = λ (x y : ⟨ M ⟩) → refl (x ·⟨ M ⟩ y)

is-magma-iso : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
is-magma-iso M N f = is-magma-hom M N f
                   × Σ \(g : ⟨ N ⟩ → ⟨ M ⟩) → is-magma-hom N M g
                                            × (g ∘ f ∼ 𝑖𝑑 ⟨ M ⟩)
                                            × (f ∘ g ∼ 𝑖𝑑 ⟨ N ⟩)

id-is-magma-iso : (M : Magma 𝓤) → is-magma-iso M M (𝑖𝑑 ⟨ M ⟩)
id-is-magma-iso M = id-is-magma-hom M ,
                    𝑖𝑑 ⟨ M ⟩ ,
                    id-is-magma-hom M ,
                    refl ,
                    refl
\end{code}

Any identification of magmas gives rise to a magma isomorphism by transport:

\begin{code}
⌜_⌝ : {M N : Magma 𝓤} → M ≡ N → ⟨ M ⟩ → ⟨ N ⟩
⌜ p ⌝ = transport ⟨_⟩ p

⌜⌝-is-iso : {M N : Magma 𝓤} (p : M ≡ N) → is-magma-iso M N (⌜ p ⌝)
⌜⌝-is-iso (refl M) = id-is-magma-iso M
\end{code}

The isomorphisms can be collected in a type:

\begin{code}
_≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
M ≅ₘ N = Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-iso M N f
\end{code}

The following function [will be](HoTT-UF-Agda.html#magmaequivalences) a bijection in the presence of
univalence, so that the identifications of magmas are in one-to-one
correspondence with the magma isomorphisms:

\begin{code}
magma-Id-to-iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
magma-Id-to-iso p = (⌜ p ⌝ , ⌜⌝-is-iso p )
\end{code}

If we omit the set-hood condition in the definition of the type of
magmas, we get the type of what we could call `∞`-magmas (then the
type of magmas could be called `0-Magma`).

\begin{code}
∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → X → X → X
\end{code}

A [monoid](https://en.wikipedia.org/wiki/Monoid) is a set equipped with an associative binary operation and
with a two-sided neutral element, and so we get the type of monoids as
follows.

We first define the three laws:

\begin{code}
left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
left-neutral e _·_ = ∀ x → e · x ≡ x

right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
right-neutral e _·_ = ∀ x → x · e ≡ x

associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z)
\end{code}

Then a monoid is a set equipped with such `e` and `_·_` satisfying these
three laws:

\begin{code}
Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoid 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X
                         × Σ \(_·_ : X → X → X)
                         → Σ \(e : X)
                         → left-neutral e _·_
                         × right-neutral e _·_
                         × associative _·_
\end{code}

*Remark.* People are more likely to use
[records](https://agda.readthedocs.io/en/latest/language/record-types.html)
in Agda rather than iterated `Σ`s as above ([recall](HoTT-UF-Agda.html#sigmatypes) that we defined
`Σ` using a record). This is fine, because records amount to iterated
`Σ` types ([recall](HoTT-UF-Agda.html#sigmatypes) that also `_×_` is a `Σ` type, by
definition). Here, however, we are being deliberately spartan. Once we
have defined our Agda notation for MLTT, we want to stick to
it. This is for teaching purposes (of MLTT, encoded in Agda, not of
Agda itself in its full glory).

We could drop the `is-set X` condition, but then we wouldn't get
`∞`-monoids in any reasonable sense. We would instead get "wild
`∞`-monoids" or "incoherent `∞`-monoids". The reason is that in
monoids (with sets as carriers) the neutrality and associativity
equations can hold in at most one way, by definition of set. But if we
drop the set-hood requirement, then the equations can hold in multiple
ways. And then one is forced to consider equations between the
identifications (all the way up in the ∞-case), which is
what "[coherence](https://ncatlab.org/nlab/show/coherence+law) data"
means. The wildness or incoherence amounts to the absence of such
data.

Similarly to the situation with magmas, identifications of monoids are
in bijection with monoid isomorphisms, assuming univalence. For this
to be the case, it is absolutely necessary that the carrier of a
monoid is a set rather than an arbitrary type, for otherwise the
monoid equations can hold in many possible ways, and we would need to
consider a notion of monoid isomorphism that in addition to preserving
the neutral element and the multiplication, preserves the identifications, and
the preservations of the identifications, and the preservation of the
preservations of the identifications, *ad infinitum*.

*Exercise.* Define the type of [groups](https://en.wikipedia.org/wiki/Group_(mathematics)) (with sets as carriers).

*Exercise.* Write down the various types of
[categories](https://en.wikipedia.org/wiki/Category_(mathematics))
defined in the HoTT book in Agda.

*Exercise.* Try to define a type of [topological
 spaces](https://en.wikipedia.org/wiki/Topological_space).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="identitytypeuf"></a> The identity type in univalent mathematics

We can view a type `X` as a sort of category with hom-types rather than
hom-sets, with the identifications between points as the arrows.

We have that `refl` provides a neutral element for composition of
identifications:

\begin{code}
refl-left : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p
\end{code}

And composition is associative:

\begin{code}
∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)
\end{code}

If we wanted to prove the above without pattern matching, this time we
would need the dependent version `J` of induction on `_≡_`.

*Exercise.* Try to do this with `J` and with `H`.

But all arrows, the identifications, are invertible:

\begin{code}
⁻¹-left∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)
\end{code}

A category in which all arrows are invertible is called a
groupoid. The above is the basis for the Hofmann--Streicher groupoid
model of type theory.

But we actually get higher groupoids, because given
identifications

   > `p q : x ≡ y`

we can consider the identity type `p ≡ q`, and given

   > `u v : p ≡ q`

we can consider the type `u ≡ v`, and so on.
See [[van den Berg and Garner](https://arxiv.org/abs/0812.0298)] and
[[Lumsdaine](https://lmcs.episciences.org/1062)].

For some types, such as the natural numbers, we [can
prove](HoTT-UF-Agda.html#naturalsset) that this process trivializes
after the first step, because the type `x ≡ y` has at most one
element. Such types are the sets as defined above.

Voevodsky defined the notion of [*hlevel*](HoTT-UF-Agda.html#hlevel)
to measure how long it takes for the process to trivialize.

Here are some more constructions with identifications:

\begin{code}
⁻¹-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)
\end{code}

The application operation on identifications is functorial, in the
sense that is preserves the neutral element and commutes with
composition.:

\begin{code}
ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)
\end{code}

This is functoriality in the second argument. We also have
functoriality in the first argument, in the following sense:

\begin{code}
ap-id : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
      → ap id p ≡ p
ap-id (refl x) = refl (refl x)

ap-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
       (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))
\end{code}

Transport is also functorial with respect to identification
composition and function composition. By construction, it maps the
neutral element to the identity function. The apparent contravariance
takes place because we have defined function composition in the usual
order, but identification composition in diagramatic order (as is
customary in each case).

\begin{code}
transport∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p
transport∙ A p (refl y) = refl (transport A p)
\end{code}

Functions of a type into a universe can be considered as generalized
presheaves, which we could perhaps call `∞`-presheaves. Their morphisms
are natural transformations:

\begin{code}
Nat : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = (x : domain A) → A x → B x
\end{code}

We don't need to specify the naturality condition, because it is
automatic:

\begin{code}
Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y) → τ y ∘ transport A p ≡ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)
\end{code}

We will have the opportunity to use the following construction a
number of times:

\begin{code}
NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)
\end{code}

\begin{code}
transport-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
               (f : X → Y) {x x' : X} (p : x ≡ x') (a : A (f x))
             → transport (A ∘ f) p a ≡ transport A (ap f p) a
transport-ap A f (refl x) a = refl a
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="dependentequality"></a> Identifications that depend on identifications

If we have an identification `p : A ≡ B` of two types `A` and `B`, and
elements `a : A` and `b : B`, we cannot ask directly whether `a ≡ b`,
because although the types are identified by `p`, they are not
necessarily the same, in the sense of definitional equality. This is
not merely a syntactical restriction of our formal system, but instead
a fundamental fact that reflects the philosophy of univalent
mathematics. For instance, consider the type

\begin{code}
data Color : 𝓤₀ ̇  where
 Black White : Color
\end{code}

With univalence, we will have that `Color ≡ 𝟚` where `𝟚` is the
[two-point type](HoTT-UF-Agda.html#binarysum) `𝟙 + 𝟙` with points `₀` and
`₁`.  But there will be two identifications `p₀ p₁ : Color ≡ 𝟚`, one
that identifies `Black` with `₀` and `White` with `₁`, and another one
that identifies `Black` with `₁` and `White` with `₀`. There is no
preferred coding of binary colors as bits.  And, precisely because of
that, even if univalence does give inhabitants of the type `Colour ≡
𝟚`, it doesn't make sense to ask whether `Black ≡ ₀` holds without
specifying one of the possible inhabitants `p₀` and `p₁`.

What we will have is that `transport id p₀` and `transport id p₁` are
the two possible bijections `Color → 𝟚` that identify colors with
bits. So, it is not enough to have `Color ≡ 𝟚` to be able to compare a
color `c : Color` with a bit `b : 𝟚`. We need to specify which
identification `p : Color ≡ 𝟚` we want to consider for the comparison.
The [same considerations](HoTT-UF-Agda.html#notsets) apply when we
consider identifications `p : 𝟚 ≡ 𝟚`.

So the meaningful comparison in the more general situation is

   > `transport id p a ≡ b`

for a specific

   > `p : A ≡ B`,

where `id` is the identity function of the universe where the types `A`
and `B` live, and hence

  > `transport id : A ≡ B → (A → B)`

is the function that transforms identifications into functions, which
has already occurred [above](HoTT-UF-Agda.html#negation).

More generally, we want to consider the situation in which we replace
the identity function `id` of the universe where `A` and `B` live by
an arbitrary type family, which is what we do now.

If we have a type

   > `X : 𝓤 ̇` ,

and a type family

   > `A : X → 𝓥 ̇`

and points

   > `x y : X`

and an identification

   > `p : x ≡ y`,

then we get the identification

   > `ap A p : A x ≡ A y`.

However, if we have

   > `a : A x`,

   > `b : A y`,

we again cannot write down the identity type

   > ~~`a ≡ b`~~ .

This is again a non-sensical mathematical statement in univalent
foundations, because the types `A x` and `A y` are not the same, but
only identified, and in general there can be many identifications, not
just `ap A p`, and so any identification between elements of `A x` and
`A y` has to be with respect to a specific identification, as in the
above particular case.

This time, the meaningful comparison, given `p : x ≡ y`, is

   > `transport A p a ≡ b`,

For example, this idea applies when comparing the values of a dependent function:

\begin{code}
apd : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : (x : X) → A x) {x y : X}
      (p : x ≡ y) → transport A p (f x) ≡ f y
apd f (refl x) = refl (f x)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="sigmaequality"></a> Equality in Σ types

With the above notion of dependent equality, we can characterize
equality in `Σ` types as follows.

\begin{code}
to-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
       → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl x , refl a) = refl (x , a)

from-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
         → σ ≡ τ
         → Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ
from-Σ-≡ (refl (x , a)) = (refl x , refl a)
\end{code}

The above gives

   > `(σ ≡ τ) ⇔ Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ`.

But this is a very weak statement when the left- and right-hand
identity types may have multiple elements, which is precisely the
point of univalent mathematics.

What we want is the lhs and the rhs to be isomorphic, or more
precisely, [equivalent in the sense of
Voevodsky](HoTT-UF-Agda.html#fibersandequivalences).

Once we have defined this notion `_≃_` of type equivalence, this
characterization will become an equivalence

   > `(σ ≡ τ) ≃ Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p pr₂ σ ≡ pr₂ τ`.

But even this is not sufficiently precise, because in general there are
many equivalences between two types. For example, there are precisely
two equivalences

   > `𝟙 + 𝟙 ≃ 𝟙 + 𝟙`,

namely the identity function and the function that flips left and
right.  What we want to say is that a *specific map* is an
equivalence.  In our case, it is the function `from-Σ-≡` defined
above.

Voevodsky came up with a definition of a type "`f` is an equivalence"
which is always a subsingleton: a given function `f` can be an
equivalence in at most one way. But we first discuss *hlevels*.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hlevel"></a> Voevodsky's notion of hlevel

Voevodsky's hlevels `0,1,2,3,...` are shifted by `2` with respect to
the `n`-groupoid numbering convention, and correspond to `-2`-groupoids
(singletons), `-1`-groupoids (subsingletons), `0`-groupoids (sets),...

First Voevodsky defined a notion of *contractible type*, which we
refer to here as *singleton type*.

\begin{code}
is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ \(c : X) → (x : X) → c ≡ x
\end{code}

Such an element `c` is called a center of contraction of `X`.

\begin{code}
𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)
\end{code}

Then the hlevel relation is defined by induction on `ℕ`, with the
induction step working with the identity types of the elements of the
type in question:

\begin{code}
_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)
\end{code}

It is often convenient in practice to have equivalent formulations of
the hlevels `1` (as subsingletons) and `2` (as sets), which we will
develop [soon](HoTT-UF-Agda.html#setscharacterization).

When working with singleton types, it will be convenient to have
distinguished names for the two projections:

\begin{code}
center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ
\end{code}

\begin{code}
singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y ⟩
                                             y ∎

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ ) → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = (x , s x)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="em"></a> The univalent principle of excluded middle

Under excluded middle, the only two subsingletons, up to equivalence,
are `𝟘` and `𝟙`. In fact, excluded middle in univalent mathematics
says precisely that.

\begin{code}
EM EM' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM  𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X
\end{code}

Notice that the above don't assert excluded middle, but instead say
what excluded middle is (like when we said what the twin-prime
conjecture is), in two logically equivalent versions:

\begin{code}
EM-gives-EM' : EM 𝓤 → EM' 𝓤
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  γ (inr x) = inr x

EM'-gives-EM : EM' 𝓤 → EM 𝓤
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr x) = inr x
\end{code}

We will not assume or deny excluded middle, which is an independent
statement (it can't be proved or disproved).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hedberg"></a> Hedberg's Theorem

To characterize sets as the types of hlevel 2, we first need to show
that subsingletons are sets, and this is not easy. We use an argument
due to
[Hedberg](https://homotopytypetheory.org/references/hedberg/). This
argument also shows that [Voevodsky's hlevels are upper
closed](HoTT-UF-Agda.html#hlevelsupper).

We choose to present an [alternative formulation of Hedberg's
Theorem](https://link.springer.com/chapter/10.1007/978-3-642-38946-7_14),
but we stress that the method of proof is essentially the same.

We first define a notion of constant map:

\begin{code}
wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'
\end{code}

The prefix "`w`" officially stands for "weakly". Perhaps
*incoherently constant* or *wildly constant* would be better
terminologies, with *coherence* understood in the `∞`-categorical
sense. We prefer to stick to *wildly* rather than *weakly*, and luckily
both start with the letter "`w`". The following is also probably not
very good terminology, but we haven't come up with a better one yet.

\begin{code}
collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ \(f : X → X) → wconstant f

collapser : (X : 𝓤 ̇ ) → collapsible X → X → X
collapser X (f , w) = f

collapser-wconstancy : (X : 𝓤 ̇ ) (c : collapsible X) → wconstant (collapser X c)
collapser-wconstancy X (f , w) = w
\end{code}

The point is that a type is a set if and only if its identity types
all have `wconstant` endomaps:

\begin{code}
Hedberg : {X : 𝓤 ̇ } (x : X)
        → ((y : X) → collapsible (x ≡ y))
        → (y : X) → is-subsingleton (x ≡ y)
Hedberg {𝓤} {X} x c y p q =
 p                       ≡⟨ a y p ⟩
 f x (refl x)⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 f x (refl x)⁻¹ ∙ f y q  ≡⟨ (a y q)⁻¹ ⟩
 q                       ∎
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = collapser (x ≡ y) (c y)
  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = collapser-wconstancy (x ≡ y) (c y)
  a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
  a x (refl x) = (⁻¹-left∙ (f x (refl x)))⁻¹
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="setscharacterization"></a> A characterization of sets

The following is immediate from the definitions:

\begin{code}
Id-collapsible : 𝓤 ̇ → 𝓤 ̇
Id-collapsible X = (x y : X) → collapsible(x ≡ y)

sets-are-Id-collapsible : (X : 𝓤 ̇ ) → is-set X → Id-collapsible X
sets-are-Id-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q
\end{code}

And the converse is the content of Hedberg's Theorem.

\begin{code}
Id-collapsibles-are-sets : (X : 𝓤 ̇ ) → Id-collapsible X → is-set X
Id-collapsibles-are-sets X c x = Hedberg x (λ y → collapser (x ≡ y) (c x y) ,
                                                  collapser-wconstancy (x ≡ y) (c x y))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="subsingletonsaresets"></a> Subsingletons are sets

In the following definition of the auxiliary function `f`, we ignore
the argument `p`, using the fact that `X` is a subsingleton instead,
to get a `wconstant` function:

\begin{code}
subsingletons-are-Id-collapsible : (X : 𝓤 ̇ ) → is-subsingleton X → Id-collapsible X
subsingletons-are-Id-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)
\end{code}

And the corollary is that subsingleton types are sets.
\begin{code}
subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = Id-collapsibles-are-sets X
                               (subsingletons-are-Id-collapsible X s)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hlevel1subsingleton"></a> The types of hlevel 1 are the subsingletons

Then with the above we get our desired characterization of the types of
hlevel `1` as an immediate consequence:

\begin{code}
subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇ ) → is-subsingleton X → X is-of-hlevel 1
subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇ ) → X is-of-hlevel 1 → is-subsingleton X
types-of-hlevel-1-are-subsingletons X = f
 where
  f : ((x y : X) → is-singleton (x ≡ y)) → (x y : X) → x ≡ y
  f s x y = center (x ≡ y) (s x y)
\end{code}

This is an "if and only if" characterization, but, under
[univalence](HoTT-UF-Agda.html#univalence), it becomes an equality
because the types under consideration are
[subsingletons](HoTT-UF-Agda.html#subsingletonsandsets).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hlevel2set"></a> The types of hlevel 2 are the sets

The same comments as for the previous section apply.

\begin{code}
sets-are-of-hlevel-2 : (X : 𝓤 ̇ ) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X = g
 where
  g : ((x y : X) → is-subsingleton (x ≡ y)) → (x y : X) → (x ≡ y) is-of-hlevel 1
  g t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)

types-of-hlevel-2-are-sets : (X : 𝓤 ̇ ) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X = f
 where
  f : ((x y : X) → (x ≡ y) is-of-hlevel 1) → (x y : X) → is-subsingleton (x ≡ y)
  f s x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (s x y)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hlevelsupper"></a> The hlevels are upper closed

A singleton is a subsingleton, a subsingleton is a set, ... , a type
of hlevel `n` is of hlevel `n+1` too, ...

Again we can conclude this almost immediately from the above development:

\begin{code}
hlevel-upper : (X : 𝓤 ̇ ) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper X zero = γ
 where
  γ : is-singleton X → (x y : X) → is-singleton (x ≡ y)
  γ h x y = p , subsingletons-are-sets X k x y p
   where
    k : is-subsingleton X
    k = singletons-are-subsingletons X h
    p : x ≡ y
    p = k x y
hlevel-upper X (succ n) = λ h x y → hlevel-upper (x ≡ y) n (h x y)
\end{code}

To be consistent with the above terminology, we have to stipulate that
all types have hlevel `∞`. We don't need a definition for this
notion. But what may happen (and it does with univalence) is that
there are types which don't have any finite hlevel. We can say that
such types then have minimal hlevel `∞`.

*Exercise.* Formulate and prove the following. The type `𝟙` has
minimal hlevel `0`.

\begin{code}
_has-minimal-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X has-minimal-hlevel 0 = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) × ¬(X is-of-hlevel n)
\end{code}

The type `𝟘` has minimal hlevel `1`, the type `ℕ` has minimal hlevel
`2`. The solution to the fact that `ℕ` has hlevel 2 is given in the
next section. More ambitiously, after
[univalence](HoTT-UF-Agda.html#univalence) is available, show that the
type of monoids has minimal hlevel `3`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="naturalsset"></a> `ℕ` is a set

Using the decidability of equality we can define a `wconstant`
function `x ≡ y → x ≡ y` and hence conclude that `ℕ` is a set. This
argument is due to Hedberg.

\begin{code}
ℕ-is-set : is-set ℕ
ℕ-is-set = Id-collapsibles-are-sets ℕ ℕ-Id-collapsible
 where
  ℕ-Id-collapsible : Id-collapsible ℕ
  ℕ-Id-collapsible x y = f (ℕ-has-decidable-equality x y) ,
                         κ (ℕ-has-decidable-equality x y)
   where
    f : (x ≡ y) + ¬(x ≡ y) → x ≡ y → x ≡ y
    f (inl p) q = p
    f (inr g) q = !𝟘 (x ≡ y) (g q)
    κ : (d : (x ≡ y) + ¬(x ≡ y)) → wconstant (f d)
    κ (inl p) q r = refl p
    κ (inr g) q r = !𝟘 (f (inr g) q ≡ f (inr g) r) (g q)
\end{code}

*Exercise.* Hedberg proved this for any type with decidable
equality. Generalize the above to account for this.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="retracts"></a> Retracts

We use retracts as a mathematical technique to transfer properties
between types. For instance, retracts of singletons are
singletons. Showing that a particular type `X` is a singleton may be
rather difficult to do directly by applying the definition of
singleton and the definition of the particular type, but it may be
easy to show that `X` is a retract of `Y` for a type `Y` that is
already known to be a singleton. In these notes, a major application
will be to get a simple proof of the known fact that invertible maps
are equivalences in the sense of Voevodsky.

A *section* of a function is simply a right inverse, by definition:

\begin{code}
has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ \(s : codomain r → domain r) → r ∘ s ∼ id
\end{code}

Notice that `has-section r` is the type of all sections `(s , η)` of `r`,
which may well be empty. So a point of this type is a designated
section `s` of `r`, together with the datum `η`. Unless the domain of `r` is a
set, this datum is not property, and we may well have an element
`(s , η')` of the type `has-section r` with `η'` distinct from `η` for the same `s`.

We say that *`X` is a retract of `Y`*, written `X ◁ Y`, if we
have a function `Y → X` which has a section:

\begin{code}
_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ \(r : Y → X) → has-section r
\end{code}

This type actually collects *all* the ways in which the type `X` can
be a retract of the type `Y`, and so is data or structure on `X` and
`Y`, rather than a property of them.

A function that has a section is called a retraction. We use this
terminology, ambiguously, also for the function that projects out the
retraction:

\begin{code}
retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y) → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X
retract-equation (r , s , η) = η

retraction-has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (ρ : X ◁ Y) → has-section (retraction ρ)
retraction-has-section (r , h) = h
\end{code}

We have an identity retraction:

\begin{code}
◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl X = 𝑖𝑑 X , 𝑖𝑑 X , refl
\end{code}

*Exercise.* The identity retraction is by no means the only retraction
of a type onto itself in general, of course. Prove that we have (that
is, produce an element of the type) `ℕ ◁ ℕ` with the function
`pred : ℕ → ℕ` defined above as the retraction.
Try to produce more inhabitants of this type.

We can define the composition of two retractions as follows:

\begin{code}
_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
  η'' = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
              r (s x)           ≡⟨ η x ⟩
              x                 ∎
\end{code}

We also define composition with an implicit argument made explicit:

\begin{code}
_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ
\end{code}

And we introduce the following postfix notation for the identity
retraction:

\begin{code}
_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = ◁-refl X
\end{code}

These last two definitions are for notational convenience. See
[below](HoTT-UF-Agda.html#fibersandequivalences) for examples of their
use.

We conclude this section with some facts about retracts of `Σ` types.
The following are technical tools for dealing with equivalences in the
sense of Voevosky in [comparison with invertible
maps](HoTT-UF-Agda.html#fibersandequivalences).

A pointwise retraction gives  a retraction of the total spaces:
\begin{code}
Σ-retract : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
          → ((x : X) → (A x) ◁ (B x)) → Σ A ◁ Σ B
Σ-retract {𝓤} {𝓥} {𝓦} {X} {A} {B} ρ = NatΣ r , NatΣ s , η'
 where
  r : (x : X) → B x → A x
  r x = retraction (ρ x)
  s : (x : X) → A x → B x
  s x = section (ρ x)
  η : (x : X) (a : A x) → r x (s x a) ≡ a
  η x = retract-equation (ρ x)
  η' : (σ : Σ A) → NatΣ r (NatΣ s σ) ≡ σ
  η' (x , a) = x , r x (s x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
               x , a           ∎
\end{code}

We have that `transport A (p ⁻¹)` is a two-sided inverse of `transport
A p` using the functoriality of `transport A`, or directly by
induction on `p`:

\begin{code}
transport-is-retraction : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                        → transport A p ∘ transport A (p ⁻¹) ∼ 𝑖𝑑 (A y)
transport-is-retraction A (refl x) = refl

transport-is-section    : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                        → transport A (p ⁻¹) ∘ transport A p ∼ 𝑖𝑑 (A x)
transport-is-section A (refl x) = refl
\end{code}

Using this, we have the following reindexing retraction of `Σ` types:

\begin{code}
Σ-reindexing-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } (r : Y → X)
                     → has-section r
                     → (Σ \(x : X) → A x) ◁ (Σ \(y : Y) → A (r y))
Σ-reindexing-retract {𝓤} {𝓥} {𝓦} {X} {Y} {A} r (s , η) = γ , φ , γφ
 where
  γ : Σ (A ∘ r) → Σ A
  γ (y , a) = (r y , a)
  φ : Σ A → Σ (A ∘ r)
  φ (x , a) = (s x , transport A ((η x)⁻¹) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (η x , transport-is-retraction A (η x) a)
\end{code}

We have defined [the property of a type being a
singleton](HoTT-UF-Agda.html#hlevel). The singleton type `Σ \(y : X) →
x ≡ y` induced by a point `x : X` of a type `X` is denoted by
`singleton-type x`. The terminology is justified by the fact that it
is indeed a singleton in the sense defined above.

\begin{code}
singleton-type : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type x = Σ \y → y ≡ x

singleton-type-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : 𝓤 ̇ } (x : X) (σ : singleton-type x)
                        → singleton-type-center x ≡ σ
singleton-type-centered x (x , refl x) = refl (x , refl x)

singleton-types-are-singletons : (X : 𝓤 ̇ ) (x : X)
                               → is-singleton (singleton-type x)
singleton-types-are-singletons X x = singleton-type-center x ,
                                     singleton-type-centered x
\end{code}

The following gives a technique for showing that some types are singletons:

\begin{code}
retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → Y ◁ X → is-singleton X → is-singleton Y
retract-of-singleton (r , s , η) (c , φ) = r c , γ
 where
  γ = λ y → r c     ≡⟨ ap r (φ (s y)) ⟩
            r (s y) ≡⟨ η y ⟩
            y       ∎
\end{code}

Sometimes we need the following symmetric versions of the above:

\begin{code}
singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' x = Σ \y → x ≡ y

singleton-type'-center : {X : 𝓤 ̇ } (x : X) → singleton-type' x
singleton-type'-center x = (x , refl x)

singleton-type'-centered : {X : 𝓤 ̇ } (x : X) (σ : singleton-type' x)
                         → singleton-type'-center x ≡ σ
singleton-type'-centered x (x , refl x) = refl (x , refl x)

singleton-types'-are-singletons : (X : 𝓤 ̇ ) (x : X)
                                → is-singleton (singleton-type' x)
singleton-types'-are-singletons X x = singleton-type'-center x ,
                                      singleton-type'-centered x
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="fibersandequivalences"></a> Voevodsky's notion of type equivalence

The main notions of univalent mathematics conceived by Voevodsky, with
formulations in MLTT, are those of [singleton
type](HoTT-UF-Agda.html#hlevel) (or contractible type),
[hlevel](HoTT-UF-Agda.html#hlevel) (including the notions of
subsingleton and set), and of type equivalence, which we define now.

We begin with a discussion of the notion of *invertible function*,
whose only difference with the notion of equivalence is that it is
data rather than property:

\begin{code}
invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)
\end{code}

The situation is that we will have a logical equivalence between "data
establishing invertibility of a given function" and "the property of
the function being an equivalence". Mathematically, what happens is
that the type "`f` is an equivalence" is a retract of the type "`f` is
invertible". This retraction property is not easy to show, and there
are many approaches. We discuss an approach we came up with while
developing these lecture notes, which is intended to be relatively
simple and direct, but the reader should consult other approaches,
such as that of the HoTT book, which has a well-established
categorical pedigree.

The problem with the notion of invertibility of `f` is that, while we
can prove that the inverse `g` is unique when it exists, we cannot in
general prove that the identification data `g ∘ f ∼ id` and `f ∘ g ∼
id` are also unique, and, indeed, [they are not in general](https://github.com/HoTT/HoTT/blob/master/contrib/HoTTBookExercises.v).

The following is Voevodsky's proposed formulation of the notion of
equivalence in MLTT, which relies on the concept of `fiber`:

\begin{code}
fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ \(x : domain f) → f x ≡ y

fiber-point : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
            → fiber f y → X
fiber-point (x , p) = x

fiber-identification : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
                     → (w : fiber f y) → f (fiber-point w) ≡ y
fiber-identification (x , p) = p
\end{code}

So the type `fiber f y` collects the points `x : X` which are mapped
to a point identified with `y`, including the identification
datum. Voevodsky's insight is that a general notion of equivalence can
be formulated in MLTT by requiring the fibers to be singletons. It is
important here that not only the `y : Y` with `f x ≡ y` is unique, but
also that the identification datum `p : f x ≡ y` is unique. This is
similar to, or even a generalization of the categorical
notion of "uniqueness up to a unique isomorphism".

\begin{code}
is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)
\end{code}

We can read this as saying that for every `y : Y` there is a unique
`x : X` with `f x ≡ y`, where the uniqueness refers not only to `x :
X` but also to the identification datum `p : f x ≡ y`.  It is easy to
see that equivalences are invertible:

\begin{code}
inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = fiber-point (center (fiber f y) (e y))

inverse-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                   → (y : Y) → f (inverse f e y) ≡ y
inverse-is-section f e y = fiber-identification (center (fiber f y) (e y))

inverse-centrality : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     (f : X → Y) (e : is-equiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , inverse-is-section f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverse-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                      → (x : X) → inverse f e (f x) ≡ x
inverse-is-retraction f e x = ap fiber-point p
 where
  p : inverse f e (f x) , inverse-is-section f e (f x) ≡ x , refl (f x)
  p = inverse-centrality f e (f x) (x , (refl (f x)))

equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f → invertible f
equivs-are-invertible f e = inverse f e ,
                            inverse-is-retraction f e ,
                            inverse-is-section f e
\end{code}

The non-trivial direction is the following, for which we use the
retraction techniques explained [above](HoTT-UF-Agda.html#retracts):

\begin{code}
invertibles-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → invertible f → is-equiv f
invertibles-are-equivs {𝓤} {𝓥} {X} {Y} f (g , η , ε) y₀ = c
 where
  a : (y : Y) → (f (g y) ≡ y₀) ◁ (y ≡ y₀)
  a y =  r , s , transport-is-section (_≡ y₀) (ε y)
   where
    r : y ≡ y₀ → f (g y) ≡ y₀
    r = transport (_≡ y₀) ((ε y)⁻¹)
    s : f (g y) ≡ y₀ → y ≡ y₀
    s = transport (_≡ y₀) (ε y)
  b : fiber f y₀ ◁ singleton-type y₀
  b = (Σ \(x : X) → f x ≡ y₀)     ◁⟨ Σ-reindexing-retract g (f , η) ⟩
      (Σ \(y : Y) → f (g y) ≡ y₀) ◁⟨ Σ-retract a ⟩
      (Σ \(y : Y) → y ≡ y₀)       ◀
  c : is-singleton (fiber f y₀)
  c = retract-of-singleton b (singleton-types-are-singletons Y y₀)
\end{code}

\begin{code}
inverse-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                 → is-equiv (inverse f e)
inverse-is-equiv f e = invertibles-are-equivs
                         (inverse f e)
                         (f , inverse-is-section f e , inverse-is-retraction f e)
\end{code}

Notice that inversion is involutive on the nose:

\begin{code}
inversion-involutive : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                     → inverse (inverse f e) (inverse-is-equiv f e) ≡ f
inversion-involutive f e = refl f
\end{code}

To see that the above procedures do exhibit the type "`f` is an
equivalence" as a retract of the type "`f` is invertible", it suffices
to show that [it is a subsingleton](HoTT-UF-Agda.html#being-equiv-is-a-subsingleton).

The identity function is invertible:
\begin{code}
id-invertible : (X : 𝓤 ̇ ) → invertible (𝑖𝑑 X)
id-invertible X = 𝑖𝑑 X , refl , refl
\end{code}

We can compose invertible maps:

\begin{code}
∘-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)
∘-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {f'} (g' , gf' , fg') (g , gf , fg) =
  g ∘ g' , η , ε
 where
  η = λ x → g (g' (f' (f x))) ≡⟨ ap g (gf' (f x)) ⟩
            g (f x)           ≡⟨ gf x ⟩
            x                 ∎

  ε = λ z → f' (f (g (g' z))) ≡⟨ ap f' (fg (g' z)) ⟩
            f' (g' z)         ≡⟨ fg' z ⟩
            z                 ∎
\end{code}

There is an identity equivalence, and we get composition of
equivalences by reduction to invertible maps:

\begin{code}
id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (𝑖𝑑 X)
id-is-equiv = singleton-types-are-singletons
\end{code}

An `abstract` definition is not expanded during type checking. One
possible use of this is efficiency. In our case, it saves 30s in the
checking of this module in the uses of `∘-is-equiv`:

\begin{code}
∘-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
           → is-equiv g → is-equiv f → is-equiv (g ∘ f)
∘-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j = γ
 where
  abstract
   γ : is-equiv (g ∘ f)
   γ = invertibles-are-equivs (g ∘ f)
         (∘-invertible (equivs-are-invertible g i)
         (equivs-are-invertible f j))
\end{code}

The type of equivalences is defined as follows:

\begin{code}
_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

Eq-to-fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq-to-fun (f , i) = f

Eq-to-fun-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (Eq-to-fun e)
Eq-to-fun-is-equiv (f , i) = i

invertibility-gives-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → invertible f → X ≃ Y
invertibility-gives-≃ f i = f , invertibles-are-equivs f i
\end{code}

Identity and composition of equivalences:

\begin{code}
≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = 𝑖𝑑 X , id-is-equiv X

_●_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverse-is-equiv f e
\end{code}

We can use the following notation for equational reasoning with equivalences:

\begin{code}
_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = ≃-refl
\end{code}

We conclude this section with some important examples.
The function `transport A p` is an equivalence.

\begin{code}
transport-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)
transport-is-equiv A (refl x) = id-is-equiv (A x)
\end{code}

Alternatively, we could have used the fact that `transport A (p ⁻¹)`
is an inverse of `transport A p`.

Here is the promised characterization of equality in `Σ` types:

\begin{code}
Σ-≡-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ τ : Σ A)
      → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
Σ-≡-≃ {𝓤} {𝓥} {X} {A}  σ τ = invertibility-gives-≃ from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ) → from-Σ-≡ (to-Σ-≡ w) ≡ w
  η (refl p , refl q) = refl (refl p , refl q)
  ε : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε (refl σ) = refl (refl σ)
\end{code}

The following are often useful:

\begin{code}
Σ-cong : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ = invertibility-gives-≃ (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε)
 where
  f : (x : X) → A x → B x
  f x = Eq-to-fun (φ x)
  g : (x : X) → B x → A x
  g x = inverse (f x) (Eq-to-fun-is-equiv (φ x))
  η : (x : X) (a : A x) → g x (f x a) ≡ a
  η x = inverse-is-retraction (f x) (Eq-to-fun-is-equiv (φ x))
  ε : (x : X) (b : B x) → f x (g x b) ≡ b
  ε x = inverse-is-section (f x) (Eq-to-fun-is-equiv (φ x))

  NatΣ-η : (w : Σ A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a) = x , g x (f x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
                   x , a           ∎

  NatΣ-ε : (t : Σ B) → NatΣ f (NatΣ g t) ≡ t
  NatΣ-ε (x , b) = x , f x (g x b) ≡⟨ ap (λ - → x , -) (ε x b) ⟩
                   x , b           ∎

≃-gives-◁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X ◁ Y
≃-gives-◁ (f , e) = (inverse f e , f , inverse-is-retraction f e)

≃-gives-▷ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ◁ X
≃-gives-▷ (f , e) = (f , inverse f e , inverse-is-section f e)

equiv-to-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → X ≃ Y → is-singleton Y → is-singleton X
equiv-to-singleton e = retract-of-singleton (≃-gives-◁ e)
\end{code}



[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="univalence"></a> Voevodsky's univalence axiom

There is a canonical transformation `(X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y` that
sends the identity identification `refl X : X ≡ X` to the identity
equivalence `≃-refl X : X ≃ X` by induction on identifications. The
univalence axiom, for the universe `𝓤`, says that this canonical map
is itself an equivalence.

\begin{code}
Id-to-Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id-to-Eq X X (refl X) = ≃-refl X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id-to-Eq X Y)
\end{code}

Thus, the univalence of the universe `𝓤` says that identifications `X
≡ Y` of types in `𝓤` are in canonical bijection with equivalences `X ≃ Y`, if by
bijection we mean equivalence, where the canonical bijection is
`Id-to-Eq`.

We emphasize that this doesn't posit that univalence holds. It says
what univalence is (like the type that says what the [twin-prime
conjecture](HoTT-UF-Agda.html#twinprime) is).

\begin{code}
is-univalent-≃ : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → (X ≡ Y) ≃ (X ≃ Y)
is-univalent-≃ ua X Y = Id-to-Eq X Y , ua X Y

Eq-to-Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq-to-Id ua X Y = inverse (Id-to-Eq X Y) (ua X Y)
\end{code}

Here is a third way to [convert a type identification into a
function](HoTT-UF-Agda.html#Id-to-Fun):

\begin{code}
Id-to-fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-fun {𝓤} {X} {Y} p = Eq-to-fun (Id-to-Eq X Y p)

Id-to-funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
                 → Id-to-fun p ≡ Id-to-Fun p
Id-to-funs-agree (refl X) = refl (𝑖𝑑 X)
\end{code}

What characterizes univalent mathematics is not the univalence
axiom. We have defined and studied the main concepts of univalent
mathematics in a pure, spartan MLTT. It is the concepts of hlevel,
including singleton, subsingleton and set, and the notion of
equivalence. Univalence *is* a fundamental ingredient, but first we
need the correct notion of equivalence to be able to formulate it.

*Remark*. If we formulate univalence with invertible maps instead of
equivalences, we get a statement that is provably false, and this is
one of the reasons why Voevodsky's notion of equivalence is
important. This is Exercise 4.6 of the [HoTT
book](https://homotopytypetheory.org/book/). There is a [solution in
Coq](https://github.com/HoTT/HoTT/blob/master/contrib/HoTTBookExercises.v)
by [Mike Shulman](https://home.sandiego.edu/~shulman/).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="notsets"></a> Example of a type that is not a set under univalence

We have two automorphisms of `𝟚`, namely the identity function and the
function that swaps ₀ and ₁:

\begin{code}
swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invertibles-are-equivs swap₂ (swap₂ , swap₂-involutive , swap₂-involutive)
\end{code}

Hence we have two distinct equivalences:

\begin{code}
e₀ e₁ : 𝟚 ≃ 𝟚
e₀ = ≃-refl 𝟚
e₁ = swap₂ , swap₂-is-equiv

e₀-is-not-e₁ : e₀ ≢ e₁
e₀-is-not-e₁ p = ₁-is-not-₀ r
 where
  q : id ≡ swap₂
  q = ap Eq-to-fun p
  r : ₁ ≡ ₀
  r = ap (λ - → - ₁) q
\end{code}

We now use an [anonymous
module](https://agda.readthedocs.io/en/latest/language/module-system.html#anonymous-modules)
to assume univalence in the next few constructions:

\begin{code}
module _ (ua : is-univalent 𝓤₀) where
\end{code}

With this assumption, we get two different identifications of the type `𝟚` with itself:

\begin{code}
  p₀ p₁ : 𝟚 ≡ 𝟚
  p₀ = Eq-to-Id ua 𝟚 𝟚 e₀
  p₁ = Eq-to-Id ua 𝟚 𝟚 e₁

  p₀-is-not-p₁ : p₀ ≢ p₁
  p₀-is-not-p₁ q = e₀-is-not-e₁ r
   where
    r = e₀              ≡⟨ (inverse-is-section (Id-to-Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
        Id-to-Eq 𝟚 𝟚 p₀ ≡⟨ ap (Id-to-Eq 𝟚 𝟚) q ⟩
        Id-to-Eq 𝟚 𝟚 p₁ ≡⟨ inverse-is-section (Id-to-Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₁ ⟩
        e₁              ∎
\end{code}

If the universe `𝓤₀` were a set, then the identifications `p₀` and
`p₁` defined above would be equal, and therefore it is not a set.

\begin{code}
  𝓤₀-is-not-a-set :  ¬(is-set (𝓤₀ ̇ ))
  𝓤₀-is-not-a-set s = p₀-is-not-p₁ q
   where
    q : p₀ ≡ p₁
    q = s 𝟚 𝟚 p₀ p₁
\end{code}

For more examples, see [[Kraus and Sattler](https://arxiv.org/abs/1311.4002)].

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="lefttothereader"></a> Exercises

Here are some facts whose proofs are left to the reader but that we
will need from the next section onwards. Sample solutions are given
[below](HoTT-UF-Agda.html#solutions).

Define functions for the following type declarations. As a matter of
procedure, we suggest to import this file and add another declaration
with the same type and new name e.g. `section-are-lc-solution`,
because we already have solutions in this file.

\begin{code}
subsingleton-criterion : {X : 𝓤 ̇ }
                       → (X → is-singleton X)
                       → is-subsingleton X

left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ≡ f x' → x ≡ x'

lc-maps-reflect-subsingletons : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → left-cancellable f
                              → is-subsingleton Y
                              → is-subsingleton X

has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ \(r : codomain s → domain s) → r ∘ s ∼ id

sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A) → has-retraction s → left-cancellable s

equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f

equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f

equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f

equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → X ≃ Y
                      → is-subsingleton Y
                      → is-subsingleton X

sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                        → has-retraction f
                        → g ∼ f
                        → has-retraction g

retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                           → has-section f
                           → g ∼ f
                           → has-section g
\end{code}

An alternative notion of equivalence, equivalent to Voevodsky's, has
been given by Andre Joyal:

\begin{code}
is-joyal-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f
\end{code}

Provide definitions for the following type declarations:

\begin{code}
joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-joyal-equiv f → invertible f

joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-joyal-equiv f → is-equiv f

invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → is-joyal-equiv f

equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g

equivs-closed-under-∼' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                       → is-equiv f
                       → f ∼ g
                       → is-equiv g

equiv-to-singleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → X ≃ Y → is-singleton X → is-singleton Y

subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                          → left-cancellable m → is-set Y → is-set X

pr₁-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-subsingleton (A x))
       → left-cancellable  (λ (t : Σ A) → pr₁ t)

subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                         → is-set X
                         → ((x : X) → is-subsingleton(A x))
                         → is-set(Σ \(x : X) → A x)

pr₁-equiv : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
         → ((x : X) → is-singleton (A x))
         → is-equiv (λ (t : Σ A) → pr₁ t)

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π \(x : X) → Σ \(a : A x) → P x a) ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))

Σ-assoc : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ }
        → Σ Z ≃ (Σ \(x : X) → Σ \(y : Y x) → Z (x , y))

⁻¹-≃ : {X : 𝓤 ̇ } (x y : X) → (x ≡ y) ≃ (y ≡ x)

singleton-types-≃ : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x

singletons-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → is-singleton X → is-singleton Y → X ≃ Y

maps-of-singletons-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → is-singleton X → is-singleton Y → is-equiv f

logically-equivalent-subsingletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                                  → is-subsingleton X
                                                  → is-subsingleton Y
                                                  → X ⇔ Y
                                                  → X ≃ Y

singletons-are-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                          → is-singleton X
                          → is-singleton Y
                          → X ≃ Y

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                 → (x : X) (b : B x) → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } (φ : Nat A B)
                                 → is-equiv (NatΣ φ)
                                 → ((x : X) → is-equiv (φ x))

Σ-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → is-subsingleton X
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Σ A)

×-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-subsingleton X
                  → is-subsingleton Y
                  → is-subsingleton (X × Y)

to-×-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
       → pr₁ z ≡ pr₁ t
       → pr₂ z ≡ pr₂ t
       → z ≡ t

×-is-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → ((Y → is-subsingleton X) × (X → is-subsingleton Y))
                   → is-subsingleton (X × Y)

×-is-subsingleton'-back : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → is-subsingleton (X × Y)
                        → (Y → is-subsingleton X) × (X → is-subsingleton Y)

ap₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x x' : X} {y y' : Y}
    → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="solutions"></a> Solutions

\begin{code}
subsingleton-criterion f x = singletons-are-subsingletons (domain f) (f x) x

lc-maps-reflect-subsingletons f l s x x' = l (s (f x) (f x'))

sections-are-lc s (r , ε) {x} {y} p = x       ≡⟨ (ε x)⁻¹ ⟩
                                      r (s x) ≡⟨ ap r p ⟩
                                      r (s y) ≡⟨ ε y ⟩
                                      y       ∎

equivs-have-retractions f e = (inverse f e , inverse-is-retraction f e)

equivs-have-sections f e = (inverse f e , inverse-is-section f e)

equivs-are-lc f e = sections-are-lc f (equivs-have-retractions f e)

equiv-to-subsingleton (f , i) = lc-maps-reflect-subsingletons f (equivs-are-lc f i)

sections-closed-under-∼ f g (r , rf) h = (r ,
                                          λ x → r (g x) ≡⟨ ap r (h x) ⟩
                                                r (f x) ≡⟨ rf x ⟩
                                                x       ∎)

retractions-closed-under-∼ f g (s , fs) h = (s ,
                                             λ y → g (s y) ≡⟨ h (s y) ⟩
                                                   f (s y) ≡⟨ fs y ⟩
                                                   y ∎)

joyal-equivs-are-invertible f ((s , fs) , (r , rf)) = (s , sf , fs)
 where
  sf = λ (x : domain f) → s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
                          r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
                          r(f x)       ≡⟨ rf x ⟩
                          x            ∎

joyal-equivs-are-equivs f j = invertibles-are-equivs f (joyal-equivs-are-invertible f j)

invertibles-are-joyal-equivs f (g , gf , fg) = ((g , fg) , (g , gf))

equivs-are-joyal-equivs f e = invertibles-are-joyal-equivs f (equivs-are-invertible f e)

equivs-closed-under-∼ f g e h =
 joyal-equivs-are-equivs g
  (retractions-closed-under-∼ f g (equivs-have-sections    f e) h ,
   sections-closed-under-∼    f g (equivs-have-retractions f e) h)

equivs-closed-under-∼' f g e h = equivs-closed-under-∼ f g e (λ x → (h x)⁻¹)

equiv-to-singleton' e = retract-of-singleton (≃-gives-▷ e)

subtypes-of-sets-are-sets {𝓤} {𝓥} {X} m i h = Id-collapsibles-are-sets X c
 where
  f : (x x' : X) → x ≡ x' → x ≡ x'
  f x x' r = i (ap m r)
  κ : (x x' : X) (r s : x ≡ x') → f x x' r ≡ f x x' s
  κ x x' r s = ap i (h (m x) (m x') (ap m r) (ap m s))
  c : Id-collapsible X
  c x x' = f x x' , κ x x'

pr₁-lc i p = to-Σ-≡ (p , i _ _ _)

subsets-of-sets-are-sets X A h p = subtypes-of-sets-are-sets pr₁ (pr₁-lc p) h

pr₁-equiv X A s = invertibles-are-equivs pr₁ (g , η , ε)
 where
  g : X → Σ A
  g x = x , pr₁(s x)
  ε : (x : X) → pr₁ (g x) ≡ x
  ε x = refl (pr₁ (g x))
  η : (σ : Σ A) → g (pr₁ σ) ≡ σ
  η (x , a) = to-Σ-≡ (ε x , singletons-are-subsingletons (A x) (s x) _ a)

ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {A} {P} = invertibility-gives-≃ φ (γ , η , ε)
 where
  φ : (Π \(x : X) → Σ \(a : A x) → P x a) → Σ \(f : Π A) → Π \(x : X) → P x (f x)
  φ g = ((λ x → pr₁ (g x)) , λ x → pr₂ (g x))
  γ : (Σ \(f : Π A) → Π \(x : X) → P x (f x)) → Π \(x : X) → Σ \(a : A x) → P x a
  γ (f , φ) x = f x , φ x
  η : γ ∘ φ ∼ id
  η = refl
  ε : φ ∘ γ ∼ id
  ε = refl

Σ-assoc {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = invertibility-gives-≃ f (g , refl , refl)
 where
  f : Σ Z → Σ \x → Σ \y → Z (x , y)
  f ((x , y) , z) = (x , (y , z))
  g : (Σ \x → Σ \y → Z (x , y)) → Σ Z
  g (x , (y , z)) = ((x , y) , z)

⁻¹-is-equiv : {X : 𝓤 ̇ } (x y : X)
            → is-equiv (λ (p : x ≡ y) → p ⁻¹)
⁻¹-is-equiv x y = invertibles-are-equivs _⁻¹ (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive)

⁻¹-≃ x y = (_⁻¹ , ⁻¹-is-equiv x y)

singleton-types-≃ x = Σ-cong (λ y → ⁻¹-≃ x y)

singletons-≃ {𝓤} {𝓥} {X} {Y} i j = invertibility-gives-≃ f (g , η , ε)
 where
  f : X → Y
  f x = center Y j
  g : Y → X
  g y = center X i
  η : (x : X) → g (f x) ≡ x
  η = centrality X i
  ε : (y : Y) → f (g y) ≡ y
  ε = centrality Y j

maps-of-singletons-are-equivs {𝓤} {𝓥} {X} {Y} f i j = invertibles-are-equivs f (g , η , ε)
 where
  g : Y → X
  g y = center X i
  η : (x : X) → g (f x) ≡ x
  η = centrality X i
  ε : (y : Y) → f (g y) ≡ y
  ε y = singletons-are-subsingletons Y j (f (g y)) y

logically-equivalent-subsingletons-are-equivalent X Y i j (f , g) =
  invertibility-gives-≃ f (g , (λ x → i (g (f x)) x) , (λ y → j (f (g y)) y))

singletons-are-equivalent X Y i j =
  invertibility-gives-≃ (λ _ → center Y j) ((λ _ → center X i) , centrality X i , centrality Y j)

NatΣ-fiber-equiv A B φ x b = invertibility-gives-≃ f (g , ε , η)
 where
  f : fiber (φ x) b → fiber (NatΣ φ) (x , b)
  f (a , refl _) = ((x , a) , refl (x , φ x a))
  g : fiber (NatΣ φ) (x , b) → fiber (φ x) b
  g ((x , a) , refl _) = (a , refl (φ x a))
  ε : (w : fiber (φ x) b) → g (f w) ≡ w
  ε (a , refl _) = refl (a , refl (φ x a))
  η : (t : fiber (NatΣ φ) (x , b)) → f (g t) ≡ t
  η ((x , a) , refl _) = refl ((x , a) , refl (NatΣ φ (x , a)))

NatΣ-equiv-gives-fiberwise-equiv {𝓤} {𝓥} {𝓦} {X} {A} {B} φ e x b = γ
 where
  d : fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
  d = NatΣ-fiber-equiv A B φ x b
  s : is-singleton (fiber (NatΣ φ) (x , b))
  s = e (x , b)
  γ : is-singleton (fiber (φ x) b)
  γ = equiv-to-singleton d s

Σ-is-subsingleton i j (x , a) (y , b) = to-Σ-≡ (i x y , j y _ _)

×-is-subsingleton i j = Σ-is-subsingleton i (λ _ → j)

to-×-≡ (refl x) (refl y) = refl (x , y)

×-is-subsingleton' {𝓤} {𝓥} {X} {Y} (i , j) = k
 where
  k : is-subsingleton (X × Y)
  k (x , y) (x' , y') = to-×-≡ (i y x x') (j x y y')

×-is-subsingleton'-back {𝓤} {𝓥} {X} {Y} k = i , j
 where
  i : Y → is-subsingleton X
  i y x x' = ap pr₁ (k (x , y) (x' , y))
  j : X → is-subsingleton Y
  j x y y' = ap pr₂ (k (x , y) (x , y'))

ap₂ f (refl x) (refl y) = refl (f x y)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="unicharac"></a> A characterization of univalence

We begin with two general results, which will be placed in a more
general context [later](HoTT-UF-Agda.html#yoneda).

\begin{code}
equiv-subsingleton-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
                         → (f : (y : X) → x ≡ y → A y)
                         → ((y : X) → is-equiv (f y))
                         → is-subsingleton (Σ A)
equiv-subsingleton-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  abstract
   e : (y : X) → (x ≡ y) ≃ A y
   e y = (f y , i y)
   d : Σ A ≃ singleton-type' x
   d = ≃-sym (Σ-cong e)
   s : is-singleton (Σ A)
   s = equiv-to-singleton d (singleton-types'-are-singletons X x)
   γ : is-subsingleton (Σ A)
   γ = singletons-are-subsingletons (Σ A) s

subsingleton-equiv-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
                         → (f : (y : X) → x ≡ y → A y)
                         → is-subsingleton (Σ A)
                         → (y : X) → is-equiv (f y)
subsingleton-equiv-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  abstract
   j : is-singleton (Σ A)
   j = pointed-subsingletons-are-singletons (Σ A) (x , (f x (refl x))) i
   g : singleton-type' x → Σ A
   g = NatΣ f
   e : is-equiv g
   e = maps-of-singletons-are-equivs g (singleton-types'-are-singletons X x) j
   γ : (y : X) → is-equiv (f y)
   γ = NatΣ-equiv-gives-fiberwise-equiv f e
\end{code}

With this we can characterize univalence as follows:

\begin{code}
univalence→ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)
univalence→ ua X = equiv-subsingleton-lemma X (Id-to-Eq X) (ua X)

→univalence : ((X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y))
            → is-univalent 𝓤
→univalence i X = subsingleton-equiv-lemma X (Id-to-Eq X) (i X)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="equivalenceinduction"></a> Equivalence induction

Under univalence, we get an induction principle for type equivalences,
corresponding to the induction principles [`H`](HoTT-UF-Agda.html#H)
and [`J`](HoTT-UF-Agda.html#J) for identifications.  To prove a
property of equivalences, it is enough to prove it for the identity
equivalence `≃-refl X` for all `X`. In order to also easily derive an
equation for this, we perform the construction using the fact that univalence implies that `Σ \(Y : 𝓤 ̇ ) → X ≃ Y` is a subsingleton for any `X`.

\begin{code}
H-≃ : is-univalent 𝓤
    → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → A X (≃-refl X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A Y e
H-≃ {𝓤} {𝓥} ua X A a Y e = τ a
 where
  B : (Σ \(Y : 𝓤 ̇ ) → X ≃ Y) → 𝓥 ̇
  B (Y , e) = A Y e
  p : (X , ≃-refl X) ≡ (Y , e)
  p = univalence→ ua X (X , ≃-refl X) (Y , e)
  τ : B (X , ≃-refl X) → B (Y , e)
  τ = transport B p

H-≃-equation : (ua : is-univalent 𝓤)
             → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
             → (a : A X  (≃-refl X))
             → H-≃ ua X A a X (≃-refl X) ≡ a
H-≃-equation {𝓤} {𝓥} ua X A a =
  H-≃ ua X A a X (≃-refl X) ≡⟨ refl _ ⟩
  transport B p a           ≡⟨ ap (λ - → transport B - a) q ⟩
  transport B (refl t) a    ≡⟨ refl _ ⟩
  a                         ∎
 where
  B : (Σ \(Y : 𝓤 ̇ ) → X ≃ Y) → 𝓥 ̇
  B (Y , e) = A Y e
  t : Σ \(Y : 𝓤 ̇ ) → X ≃ Y
  t = (X , ≃-refl X)
  p : t ≡ t
  p = univalence→ ua X t t
  q : p ≡ refl t
  q = subsingletons-are-sets (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)
       (univalence→ ua X) t t p (refl t)
\end{code}

The induction principle `H-≃` keeps `X` fixed and lets `Y` vary, while
the induction principle `J-≃` lets both vary:

\begin{code}
J-≃ : is-univalent 𝓤
    → (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → ((X : 𝓤 ̇ ) → A X X (≃-refl X))
    → (X Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e
J-≃ ua A φ X = H-≃ ua X (A X) (φ X)
\end{code}

A second set of equivalence induction principles refer to `is-equiv`
rather than `≃` and are proved by reduction to the first version
`H-≃`:

\begin{code}
H-equiv : is-univalent 𝓤
        → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
        → A X (𝑖𝑑 X) → (Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A Y f
H-equiv {𝓤} {𝓥} ua X A a Y f i = γ (f , i) i
 where
  B : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓤 ⊔ 𝓥 ̇
  B Y (f , i) = is-equiv f → A Y f
  b : B X (≃-refl X)
  b = λ (_ : is-equiv (𝑖𝑑 X)) → a
  γ : (e : X ≃ Y) → B Y e
  γ = H-≃ ua X B b Y
\end{code}

The above and the following say that to prove that a property of
functions holds for all equivalences, it is enough to prove it for all
identity functions:

\begin{code}
J-equiv : is-univalent 𝓤
        → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
        → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
        → (X Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A X Y f
J-equiv ua A φ X = H-equiv ua X (A X) (φ X)
\end{code}

And the following is an immediate consequence of the fact that
invertible maps are equivalences:

\begin{code}
J-invertible : is-univalent 𝓤
             → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
             → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
             → (X Y : 𝓤 ̇ ) (f : X → Y) → invertible f → A X Y f
J-invertible ua A φ X Y f i = J-equiv ua A φ X Y f (invertibles-are-equivs f i)
\end{code}

Here is an example:

\begin{code}
Σ-change-of-variables' : is-univalent 𝓤
                       → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (f : X → Y)
                       → (i : is-equiv f)
                       → (Σ \(x : X) → A x) ≡ (Σ \(y : Y) → A (inverse f i y))
Σ-change-of-variables' {𝓤} {𝓥} ua {X} {Y} A f i = H-≃ ua X B b Y (f , i)
 where
   B : (Y : 𝓤 ̇ ) → X ≃ Y →  (𝓤 ⊔ 𝓥)⁺ ̇
   B Y (f , i) = (Σ A) ≡ (Σ (A ∘ inverse f i))
   b : B X (≃-refl X)
   b = refl (Σ A)
\end{code}

The above version using the inverse of `f` can be proved directly by
induction, but the following version is perhaps more natural.

\begin{code}
Σ-change-of-variables : is-univalent 𝓤
                      → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : Y → 𝓥 ̇ ) (f : X → Y)
                      → is-equiv f
                      → (Σ \(y : Y) → A y) ≡ (Σ \(x : X) → A (f x))
Σ-change-of-variables ua A f i = Σ-change-of-variables' ua A
                                    (inverse f i)
                                    (inverse-is-equiv f i)
\end{code}

This particular proof works only because inversion [is involutive on
the nose](HoTT-UF-Agda.html#inversion-involutive).

As another example we have the following:
\begin{code}
transport-map-along-≡ : {X Y Z : 𝓤 ̇ } (p : X ≡ Y) (g : X → Z)
                      → transport (λ - → - → Z) p g
                      ≡ g ∘ Id-to-fun (p ⁻¹)
transport-map-along-≡ (refl X) = refl

transport-map-along-≃ : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (e : X ≃ Y) (g : X → Z)
                      → transport (λ - → - → Z) (Eq-to-Id ua X Y e) g
                      ≡ g ∘ Eq-to-fun (≃-sym e)
transport-map-along-≃ {𝓤} ua {X} {Y} {Z} = J-≃ ua A a X Y
 where
  A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓤 ̇
  A X Y e = (g : X → Z) → transport (λ - → - → Z) (Eq-to-Id ua X Y e) g
                        ≡ g ∘ Eq-to-fun (≃-sym e)
  a : (X : 𝓤 ̇ ) → A X X (≃-refl X)
  a X g = transport (λ - → - → Z) (Eq-to-Id ua X X (≃-refl X)) g ≡⟨ q ⟩
          transport (λ - → - → Z) (refl X) g                     ≡⟨ refl _ ⟩
          g                                                      ∎
    where
     p : Eq-to-Id ua X X (≃-refl X) ≡ refl X
     p = inverse-is-retraction (Id-to-Eq X X) (ua X X) (refl X)
     q = ap (λ - → transport (λ - → - → Z) - g ) p
\end{code}

An annoying feature of the use of `J` (rather than pattern matching on
`refl`) or `J-≃` is that we have to repeat what we want to prove, as
in the above example.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="haes"></a> Half adjoint equivalences

An often useful alternative formulation of the notion of equivalence
is that of half adjoint equivalence. If we have a function `f : X → Y`
with inversion data `g : Y → X` and `η : g ∘ f ∼ id` and `ε : f ∘ g ∼
id`, then for any `x : X` we have that

   > `ap f (η x)` and `ε (f x)`

are two identifications of type

   > `f (g (f x)) ≡ f x`.

The half adjoint condition says that these two identifications are
themselves identified. The addition of the constraint

   > `τ x : ap f (η x) ≡ ε (f x)`

turns invertibility, which is data in general, into property of `f`,
as discussed in the HoTT book.

\begin{code}
is-hae : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-hae f = Σ \(g : codomain f → domain f)
         → Σ \(η : g ∘ f ∼ id)
         → Σ \(ε : f ∘ g ∼ id)
         → (x : domain f) → ap f (η x) ≡ ε (f x)
\end{code}

The following just forgets the constraint `τ`:

\begin{code}
haes-are-invertible : {X Y : 𝓤 ̇ } (f : X → Y)
                    → is-hae f → invertible f
haes-are-invertible f (g , η , ε , τ) = g , η , ε

haes-are-equivs : {X Y : 𝓤 ̇ } (f : X → Y)
                → is-hae f → is-equiv f
haes-are-equivs f i = invertibles-are-equivs f (haes-are-invertible f i)
\end{code}

To recover the constraint for all invertible maps, under univalence, it is
enough to give the constraint for identity maps:

\begin{code}
id-is-hae : (X : 𝓤 ̇ ) → is-hae (𝑖𝑑 X)
id-is-hae X = 𝑖𝑑 X , refl , refl , (λ x → refl (refl x))

equivs-are-haes : is-univalent 𝓤
                → {X Y : 𝓤 ̇ } (f : X → Y)
                → is-equiv f → is-hae f
equivs-are-haes ua {X} {Y} = J-equiv ua (λ X Y f → is-hae f) id-is-hae X Y

invertibles-are-haes : is-univalent 𝓤
                     → {X Y : 𝓤 ̇ } (f : X → Y)
                     → invertible f → is-hae f
invertibles-are-haes ua f i = equivs-are-haes ua f (invertibles-are-equivs f i)
\end{code}

The above can be proved without univalence, as is done in the HoTT
book, with a more complicated argument coming from [category theory](https://ncatlab.org/nlab/show/adjoint+equivalence).

Here is a use of the half adjoint condition, where, compared to
[`Σ-change-of-variables`](HoTT-UF-Agda.html#Σ-change-of-variables), we
remove univalence from the hypothesis, generalize the universe of the
type `Y`, and weaken equality to equivalence in the conclusion. Notice
that the proof starts as that of
[`Σ-reindexing-retract`](HoTT-UF-Agda.html#Σ-reindexing-retract).

\begin{code}
Σ-change-of-variables-hae : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                          → is-hae f → Σ A ≃ Σ (A ∘ f)
Σ-change-of-variables-hae A f (g , η , ε , τ) = φ , invertibles-are-equivs φ (γ , γφ , φγ)
 where
  φ : Σ A → Σ (A ∘ f)
  φ (y , a) = (g y , transport A ((ε y)⁻¹) a)
  γ : Σ (A ∘ f) → Σ A
  γ (x , a) = (f x , a)
  γφ : (z : Σ A) → γ (φ z) ≡ z
  γφ (y , a) = to-Σ-≡ (ε y , transport-is-retraction A (ε y) a)
  φγ : (t : Σ (A ∘ f)) → φ (γ t) ≡ t
  φγ (x , a) = to-Σ-≡ (η x , q)
   where
    b : A (f (g (f x)))
    b = transport A ((ε (f x))⁻¹) a

    q = transport (A ∘ f) (η x)  b ≡⟨ transport-ap A f (η x) b ⟩
        transport A (ap f (η x)) b ≡⟨ ap (λ - → transport A - b) (τ x) ⟩
        transport A (ε (f x))    b ≡⟨ transport-is-retraction A (ε (f x)) a ⟩
        a                          ∎
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="funextfromua"></a> Function extensionality from univalence

Function extensionality says that any two pointwise equal functions
are equal. This is known to be not provable or disprovable in
MLTT. It is an independent statement, which we abbreviate as `funext`.

\begin{code}
funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g
\end{code}

There [will be](HoTT-UF-Agda.html#hfunext) two seemingly stronger
statements, namely the generalization to dependent functions, and the
requirement that the canonical map `(f ≡ g) → (f ∼ g)` is an
equivalence.

*Exercise.* Assuming `funext`, prove that if `f : X → Y` is an equivalence
then so is the function `(-) ∘ f : (Y → Z) → (X → Z)`.

The crucial step in [Voevodsky's
proof](http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf)
that univalence implies `funext` is to establish the conclusion of the
above exercise assuming univalence instead. We prove this by
[equivalence induction](HoTT-UF-Agda.html#equivalenceinduction) on
`f`, which means that we only need to consider the case when `f` is an
identity function, for which pre-composition with `f` is itself an
identity function (of a function type), and hence an equivalence:

\begin{code}
pre-comp-is-equiv : is-univalent 𝓤
                  → (X Y : 𝓤 ̇ ) (f : X → Y)
                  → is-equiv f
                  → (Z : 𝓤 ̇ ) → is-equiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv {𝓤} ua =
   J-equiv ua
     (λ X Y (f : X → Y) → (Z : 𝓤 ̇ ) → is-equiv (λ g → g ∘ f))
     (λ X Z → id-is-equiv (X → Z))
\end{code}

With this we can prove the desired result as follows.

\begin{code}
univalence-gives-funext : is-univalent 𝓤 → funext 𝓥 𝓤
univalence-gives-funext ua {X} {Y} {f₀} {f₁} = γ
 where
  Δ = Σ \(y₀ : Y) → Σ \(y₁ : Y) → y₀ ≡ y₁

  δ : Y → Δ
  δ y = (y , y , refl y)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = invertibles-are-equivs δ (π₀ , η , ε)
   where
    η : (y : Y) → π₀ (δ y) ≡ y
    η y = refl y
    ε : (d : Δ) → δ (π₀ d) ≡ d
    ε (y , y , refl y) = refl (y , y , refl y)

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = pre-comp-is-equiv ua Y Δ δ δ-is-equiv Y

  p : φ π₀ ≡ φ π₁
  p = refl (𝑖𝑑 Y)

  q : π₀ ≡ π₁
  q = equivs-are-lc φ φ-is-equiv p

  γ : f₀ ∼ f₁ → f₀ ≡ f₁
  γ h = ap (λ π x → π (f₀ x , f₁ x , h x)) q
\end{code}

This definition of `γ` is probably too quick. Here are all the steps
performed silently by Agda, by expanding judgmental equalities,
indicated with `refl` here:

\begin{code}
  γ' : f₀ ∼ f₁ → f₀ ≡ f₁
  γ' h = f₀                              ≡⟨ refl _ ⟩
         (λ x → f₀ x)                    ≡⟨ refl _ ⟩
         (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) q ⟩
         (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl _ ⟩
         (λ x → f₁ x)                    ≡⟨ refl _ ⟩
         f₁                              ∎
\end{code}

So notice that this relies on the so-called η-rule for judgmental
equality of functions, namely `f = λ x → f x`. Without it, we would
only get that

   > `f₀ ∼ f₁ → (λ x → f₀ x) ≡ (λ x → f₁ x)`

instead.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hfunext"></a> Variations of function extensionality and their logical equivalence

Dependent function extensionality:

\begin{code}
dfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g
\end{code}

The above says that there is some map `f ~ g → f ≡ g`. The following
instead says that the canonical map in the other direction is an
equivalence:

\begin{code}
happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)
\end{code}

Voevodsky showed that all notions of function extensionality are
logically equivalent to saying that products of singletons are
singletons:

\begin{code}
vvfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-singleton (A x)) → is-singleton (Π A)

dfunext-gives-vvfunext : dfunext 𝓤 𝓥 → vvfunext 𝓤 𝓥
dfunext-gives-vvfunext fe {X} {A} i = f , c
 where
  f : Π A
  f x = center (A x) (i x)
  c : (g : Π A) → f ≡ g
  c g = fe (λ (x : X) → centrality (A x) (i x) (g x))
\end{code}

We need some lemmas to get `hfunext` from `vvfunext`:

\begin{code}
post-comp-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                     → funext 𝓦 𝓤 → funext 𝓦 𝓥
                     → (f : X → Y) → invertible f → invertible (λ (h : A → X) → f ∘ h)
post-comp-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

post-comp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → funext 𝓦 𝓤 → funext 𝓦 𝓥
                   → (f : X → Y) → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)
post-comp-is-equiv fe fe' f e =
 invertibles-are-equivs
  (λ h → f ∘ h)
  (post-comp-invertible fe fe' f (equivs-are-invertible f e))

vvfunext-gives-hfunext : vvfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
vvfunext-gives-hfunext vfe {X} {Y} f = γ
 where
  a : (x : X) → is-singleton (Σ \(y : Y x) → f x ≡ y)
  a x = singleton-types'-are-singletons (Y x) (f x)
  c : is-singleton ((x : X) → Σ \(y : Y x) → f x ≡ y)
  c = vfe a
  R : (Σ \(g : Π Y) → f ∼ g) ◁ (Π \(x : X) → Σ \(y : Y x) → f x ≡ y)
  R = ≃-gives-▷ ΠΣ-distr-≃
  r : (Π \(x : X) → Σ \(y : Y x) → f x ≡ y) → Σ \(g : Π Y) → f ∼ g
  r = λ _ → f , (λ x → refl (f x))
  d : is-singleton (Σ \(g : Π Y) → f ∼ g)
  d = retract-of-singleton R c
  e : (Σ \(g : Π Y) → f ≡ g) → (Σ \(g : Π Y) → f ∼ g)
  e = NatΣ (happly f)
  i : is-equiv e
  i = maps-of-singletons-are-equivs e (singleton-types'-are-singletons (Π Y) f) d
  γ : (g : Π Y) → is-equiv (happly f g)
  γ = NatΣ-equiv-gives-fiberwise-equiv (happly f) i
\end{code}

And finally the seemingly rather weak, non-dependent version `funext`
implies the seemingly strongest version, which closes the circle of
logical equivalences.

\begin{code}
funext-gives-vvfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → vvfunext 𝓤 𝓥
funext-gives-vvfunext {𝓤} {𝓥} fe fe' {X} {A} φ = γ
 where
  f : Σ A → X
  f = pr₁
  f-is-equiv : is-equiv f
  f-is-equiv = pr₁-equiv X A φ
  g : (X → Σ A) → (X → X)
  g h = f ∘ h
  g-is-equiv : is-equiv g
  g-is-equiv = post-comp-is-equiv fe fe' f f-is-equiv
  i : is-singleton (Σ \(h : X → Σ A) → f ∘ h ≡ 𝑖𝑑 X)
  i = g-is-equiv (𝑖𝑑 X)
  r : (Σ \(h : X → Σ A) → f ∘ h ≡ 𝑖𝑑 X) → Π A
  r (h , p) x = transport A (happly (f ∘ h) (𝑖𝑑 X) p x) (pr₂ (h x))
  s : Π A → (Σ \(h : X → Σ A) → f ∘ h ≡ 𝑖𝑑 X)
  s φ = (λ x → x , φ x) , refl (𝑖𝑑 X)
  rs : ∀ φ → r (s φ) ≡ φ
  rs φ = refl (r (s φ))
  γ : is-singleton (Π A)
  γ = retract-of-singleton (r , s , rs) i
\end{code}

We have the following corollaries. We first formulate the types of
some functions:

\begin{code}
funext-gives-hfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → hfunext 𝓤 𝓥
dfunext-gives-hfunext      : dfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
funext-gives-dfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → dfunext 𝓤 𝓥
univalence-gives-dfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
univalence-gives-hfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → hfunext 𝓤 𝓥
univalence-gives-vvfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → vvfunext 𝓤 𝓥
univalence-gives-hfunext   : is-univalent 𝓤 → hfunext 𝓤 𝓤
univalence-gives-dfunext   : is-univalent 𝓤 → dfunext 𝓤 𝓤
univalence-gives-vvfunext  : is-univalent 𝓤 → vvfunext 𝓤 𝓤
\end{code}

And then we give their definitions (Agda makes sure there are no circularities):

\begin{code}
funext-gives-hfunext fe fe' = vvfunext-gives-hfunext (funext-gives-vvfunext fe fe')

funext-gives-dfunext fe fe' = hfunext-gives-dfunext (funext-gives-hfunext fe fe')

dfunext-gives-hfunext fe = vvfunext-gives-hfunext (dfunext-gives-vvfunext fe)

univalence-gives-dfunext' ua ua' = funext-gives-dfunext
                                    (univalence-gives-funext ua')
                                    (univalence-gives-funext ua)

univalence-gives-hfunext' ua ua' = funext-gives-hfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

univalence-gives-vvfunext' ua ua' = funext-gives-vvfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

univalence-gives-hfunext ua = univalence-gives-hfunext' ua ua

univalence-gives-dfunext ua = univalence-gives-dfunext' ua ua

univalence-gives-vvfunext ua = univalence-gives-vvfunext' ua ua
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="typeclassifier"></a> Universes are map classifiers

Under univalence, a universe `𝓤` becomes a map classifier, in the
sense that maps from a type in `𝓤` into a type `Y : 𝓤` are in
canonical bijection with functions `Y → 𝓤`. Using the following
*slice* notation, this amounts to a bijection between `𝓤 / Y` and `Y → 𝓤`:

\begin{code}
_/_ : (𝓤 : Universe) → 𝓤 ̇ → 𝓤 ⁺ ̇
𝓤 / Y = Σ \(X : 𝓤 ̇ ) → X → Y
\end{code}

We need the following lemma, which has other uses:
\begin{code}
total-fiber-is-domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → Σ (fiber f) ≃ X
total-fiber-is-domain {𝓤} {𝓥} {X} {Y} f = invertibility-gives-≃ g (h , η , ε)
 where
  g : (Σ \(y : Y) → Σ \(x : X) → f x ≡ y) → X
  g (y , x , p) = x
  h : X → Σ \(y : Y) → Σ \(x : X) → f x ≡ y
  h x = (f x , x , refl (f x))
  η : ∀ t → h (g t) ≡ t
  η (_ , x , refl _) = refl (f x , x , refl _)
  ε : (x : X) → g (h x) ≡ x
  ε = refl
\end{code}

We define the desired canonical bijection in a submodule with
assumptions:

\begin{code}
module map-classifier
        (𝓤 : Universe)
        (ua : is-univalent 𝓤)
        (fe : dfunext 𝓤 (𝓤 ⁺))
        (Y : 𝓤 ̇ )
       where
\end{code}

The function `χ` gives the *characteristic function* of a map into `Y`:

\begin{code}
 χ : 𝓤 / Y  → (Y → 𝓤 ̇ )
 χ (X , f) = fiber f
\end{code}

Any `Y → 𝓤` is the characteristic map of some map into `Y`:

\begin{code}
 T : (Y → 𝓤 ̇ ) → 𝓤 / Y
 T A = Σ A , pr₁
\end{code}

And these constructions are mutually inverse:

\begin{code}
 χη : (σ : 𝓤 / Y) → T (χ σ) ≡ σ
 χη (X , f) = r
  where
   e : Σ (fiber f) ≃ X
   e = total-fiber-is-domain f
   p : Σ (fiber f) ≡ X
   p = Eq-to-Id ua (Σ (fiber f)) X e
   observation : Eq-to-fun (≃-sym e) ≡ (λ x → f x , x , refl (f x))
   observation = refl _
   q = transport (λ - → - → Y) p pr₁ ≡⟨ transport-map-along-≃ ua e pr₁ ⟩
       pr₁ ∘ Eq-to-fun (≃-sym e)     ≡⟨ refl _ ⟩
       f                             ∎
   r : (Σ (fiber f) , pr₁) ≡ (X , f)
   r = to-Σ-≡ (p , q)

 χε : (A : Y → 𝓤 ̇ ) → χ (T A) ≡ A
 χε A = fe γ
  where
   f : ∀ y → fiber pr₁ y → A y
   f y ((y , a) , refl p) = a
   g : ∀ y → A y → fiber pr₁ y
   g y a = (y , a) , refl y
   η : ∀ y σ → g y (f y σ) ≡ σ
   η y ((y , a) , refl p) = refl ((y , a) , refl p)
   ε : ∀ y a → f y (g y a) ≡ a
   ε y a = refl a
   γ : ∀ y → fiber pr₁ y ≡ A y
   γ y = Eq-to-Id ua (fiber pr₁ y) (A y) (invertibility-gives-≃ (f y) (g y , η y , ε y))

 χ-is-equiv : is-equiv χ
 χ-is-equiv = invertibles-are-equivs χ (T , χη , χε)

 canonical-bijection : 𝓤 / Y ≃ (Y → 𝓤 ̇ )
 canonical-bijection = χ , χ-is-equiv
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="univalencesubsingleton"></a> The univalence axiom is a (sub)singleton

If we use a type as an axiom, it should better have at most one element. We
prove some generally useful lemmas first.

\begin{code}
Π-is-subsingleton : dfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Π A)
Π-is-subsingleton fe i f g = fe (λ x → i x (f x) (g x))

being-singleton-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ }
                                  → is-subsingleton (is-singleton X)
being-singleton-is-a-subsingleton fe {X} (x , φ) (y , γ) = p
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)
  s : is-set X
  s = subsingletons-are-sets X i
  p : (x , φ) ≡ (y , γ)
  p = to-Σ-≡ (φ y , fe (λ (z : X) → s y z _ _))

being-equiv-is-a-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → is-subsingleton (is-equiv f)
being-equiv-is-a-subsingleton fe fe' f = Π-is-subsingleton fe
                                          (λ x → being-singleton-is-a-subsingleton fe')

univalence-is-a-subsingleton : is-univalent (𝓤 ⁺) → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingleton {𝓤} ua⁺ ua ua' = p
 where
  fe₀  :  funext  𝓤     𝓤
  fe₁  :  funext  𝓤    (𝓤 ⁺)
  fe₂  :  funext (𝓤 ⁺) (𝓤 ⁺)
  dfe₁ : dfunext  𝓤    (𝓤 ⁺)
  dfe₂ : dfunext (𝓤 ⁺) (𝓤 ⁺)

  fe₀  = univalence-gives-funext ua
  fe₁  = univalence-gives-funext {𝓤 ⁺} {𝓤}   ua⁺
  fe₂  = univalence-gives-funext {𝓤 ⁺} {𝓤 ⁺} ua⁺
  dfe₁ = funext-gives-dfunext fe₁ fe₀
  dfe₂ = funext-gives-dfunext fe₂ fe₂

  i : is-subsingleton (is-univalent 𝓤)
  i = Π-is-subsingleton dfe₂
       (λ X → Π-is-subsingleton dfe₂
               (λ Y → being-equiv-is-a-subsingleton dfe₁ dfe₂ (Id-to-Eq X Y)))

  p : ua ≡ ua'
  p = i ua ua'
\end{code}

So if all universes are univalent then "being univalent" is a
subsingleton, and hence a singleton. This hypothesis of global
univalence cannot be expressed in our MLTT that only has `ω`
many universes, because global univalence would have to live in the
first universe after them. Agda [does have](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set) such a universe `𝓤ω,` and so
we can formulate it here. There would be no problem in extending our
MLTT to have such a universe if we so wished, in which case we would
be able to formulate and prove:

\begin{code}
Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-a-subsingletonω : Univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingletonω {𝓤} γ = univalence-is-a-subsingleton (γ (𝓤 ⁺))

univalence-is-a-singleton : Univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-singleton {𝓤} γ = pointed-subsingletons-are-singletons
                                   (is-univalent 𝓤)
                                   (γ 𝓤)
                                   (univalence-is-a-subsingletonω γ)
\end{code}

That the type `univalence` would be a subsingleton can't even
be formulated in the absence of a successor `𝓤ω⁺` of `𝓤ω`, and Agda
doesn't have such a successor universe (but there isn't any fundamental reason why it couldn't have it).

In the absence of a universe `𝓤ω` in our MLTT, we can simply have an
[axiom schema](https://en.wikipedia.org/wiki/Axiom_schema), consisting
of `ω`-many axioms, stating that each universe is univalent. Then we
can prove in our MLTT that the univalence property for each inverse is
a (sub)singleton, with `ω`-many proofs (or just one schematic proof
with a free variable for a universe `𝓤ₙ`).

It follows immediately from the above that global univalence gives
global function extensionality:

\begin{code}
global-dfunext : 𝓤ω
global-dfunext = ∀ {𝓤 𝓥} → dfunext 𝓤 𝓥

univalence-gives-global-dfunext : Univalence → global-dfunext
univalence-gives-global-dfunext ua {𝓤} {𝓥} = univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

global-hfunext : 𝓤ω
global-hfunext = ∀ {𝓤 𝓥} → hfunext 𝓤 𝓥

univalence-gives-global-hfunext : Univalence → global-hfunext
univalence-gives-global-hfunext ua {𝓤} {𝓥} = univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⊔ 𝓥))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hfunextsubsingleton"></a> `hfunext` and `vvfunext` are subsingletons

This is left as an exercise. Like univalence, the proof that these two
forms of function extensional extensionality require assumptions of
function extensionality at higher universes. So perhaps it is more
convenient to just assume global univalence. An inconvenience is that
the natural tool to use, Π-is-subsingleton, needs products with
explicit arguments, but we made some of the arguments of hfunext and
vvfunext implicit. One way around this problem is to define equivalent
versions with the arguments explicit, and establish an equivalence
between the new version and the original version.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="morefunextuses"></a> More consequences of function extensionality

\begin{code}
being-subsingleton-is-a-subsingleton : {X : 𝓤 ̇ } → dfunext 𝓤 𝓤
                                     → is-subsingleton (is-subsingleton X)
being-subsingleton-is-a-subsingleton {𝓤} {X} fe i j = c
 where
  l : is-set X
  l = subsingletons-are-sets X i
  a : (x y : X) → i x y ≡ j x y
  a x y = l x y (i x y) (j x y)
  b : (x : X) → i x ≡ j x
  b x = fe (a x)
  c : i ≡ j
  c = fe b
\end{code}

Here is a situation where `hfunext` is what is needed:

\begin{code}
Π-is-set : hfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = hfunext-gives-dfunext hfe ((λ x → s x (f x) (g x) (p x) (q x)))
  b : is-subsingleton(f ≡ g)
  b = equiv-to-subsingleton (happly f g , hfe f g) a

being-set-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-subsingleton (is-set X)
being-set-is-a-subsingleton fe = Π-is-subsingleton fe
                                  (λ x → Π-is-subsingleton fe
                                          (λ y → being-subsingleton-is-a-subsingleton fe))
\end{code}

More generally:

\begin{code}
hlevel-relation-is-a-subsingleton : dfunext 𝓤 𝓤
                                  → (n : ℕ) (X : 𝓤 ̇ )
                                  → is-subsingleton (X is-of-hlevel n)
hlevel-relation-is-a-subsingleton {𝓤} fe zero     X = being-singleton-is-a-subsingleton fe
hlevel-relation-is-a-subsingleton fe (succ n) X =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
          (λ x' → hlevel-relation-is-a-subsingleton fe n (x ≡ x')))
\end{code}

Composition of equivalences is associative:

\begin{code}
●-assoc : dfunext 𝓣 (𝓤 ⊔ 𝓣) → dfunext (𝓤 ⊔ 𝓣) (𝓤 ⊔ 𝓣)
        → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
          (α : X ≃ Y) (β : Y ≃ Z) (γ : Z ≃ T)
        → α ● (β ● γ) ≡ (α ● β) ● γ
●-assoc fe fe' (f , a) (g , b) (h , c) = ap (h ∘ g ∘ f ,_) q
 where
  d e : is-equiv (h ∘ g ∘ f)
  d = ∘-is-equiv (∘-is-equiv c b) a
  e = ∘-is-equiv c (∘-is-equiv b a)

  q : d ≡ e
  q = being-equiv-is-a-subsingleton fe fe' (h ∘ g ∘ f) _ _

≃-sym-involutive : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) →
                   {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                 → ≃-sym (≃-sym α) ≡ α
≃-sym-involutive fe fe' (f , a) = to-Σ-≡ (inversion-involutive f a ,
                                          being-equiv-is-a-subsingleton fe fe' f _ _)
\end{code}

*Exercise.* The hlevels are closed under `Σ` and, using `hfunext`, also
under `Π`. Univalence is not needed, but makes the proof easier.  (Without
univalence, we need to show that hlevels are
closed under equivalence first.)

\begin{code}
Π-cong : dfunext 𝓤 𝓥 → dfunext 𝓤 𝓦
       → (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) (Y' : X → 𝓦 ̇ )
       → ((x : X) → Y x ≃ Y' x) → Π Y ≃ Π Y'
Π-cong fe fe' X Y Y' φ = invertibility-gives-≃ F (G , GF , FG)
 where
  f : (x : X) → Y x → Y' x
  f x = Eq-to-fun (φ x)
  e : (x : X) → is-equiv (f x)
  e x = Eq-to-fun-is-equiv (φ x)
  g : (x : X) → Y' x → Y x
  g x = inverse (f x) (e x)
  fg : (x : X) (y' : Y' x) → f x (g x y') ≡ y'
  fg x = inverse-is-section (f x) (e x)
  gf : (x : X) (y : Y x) → g x (f x y) ≡ y
  gf x = inverse-is-retraction (f x) (e x)

  F : ((x : X) → Y x) → ((x : X) → Y' x)
  F φ x = f x (φ x)
  G : ((x : X) → Y' x) → (x : X) → Y x
  G γ x = g x (γ x)
  FG :  (γ : ((x : X) → Y' x)) → F(G γ) ≡ γ
  FG γ = fe' (λ x → fg x (γ x))
  GF : (φ : ((x : X) → Y x)) → G(F φ) ≡ φ
  GF φ = fe (λ x → gf x (φ x))

pre-comp-invertible : dfunext 𝓥 𝓦 → dfunext 𝓤 𝓦
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y)
                    → invertible f
                    → invertible (λ (h : Y → Z) → h ∘ f)
pre-comp-invertible fe fe' {X} {Y} {Z} f (g , η , ε) = (g' , η' , ε')
 where
  f' : (Y → Z) → (X → Z)
  f' h = h ∘ f
  g' : (X → Z) → (Y → Z)
  g' k = k ∘ g
  η' : (h : Y → Z) → g' (f' h) ≡ h
  η' h = fe (λ y → ap h (ε y))
  ε' : (k : X → Z) → f' (g' k) ≡ k
  ε' k = fe' (λ x → ap k (η x))
\end{code}

Recall that a function is a [Joyal
equivalence](HoTT-UF-Agda.html#is-joyal-equiv) if it has a section and
it has a retraction. We now show that this notion is a singleton.  For
that purpose, we first show that if a function has a retraction then
it has at most one section, and that if it has a section then it has
at most one retraction.

\begin{code}
retraction-has-at-most-one-section : dfunext 𝓥 𝓤 → hfunext 𝓥 𝓥
                                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → has-retraction f
                                   → is-subsingleton (has-section f)
retraction-has-at-most-one-section {𝓥} {𝓤} fe hfe {X} {Y} f (g , gf) (h , fh) = d
 where
  fe' : dfunext 𝓥 𝓥
  fe' = hfunext-gives-dfunext hfe
  a : invertible f
  a = joyal-equivs-are-invertible f (((h , fh) , g , gf))
  b : is-singleton (fiber (λ h →  f ∘ h) id)
  b = invertibles-are-equivs (λ h → f ∘ h) (post-comp-invertible fe fe' f a) id
  r : fiber (λ h →  f ∘ h) id → has-section f
  r (h , p) = (h , happly (f ∘ h) id p)
  s : has-section f → fiber (λ h → f ∘ h) id
  s (h , η) = (h , fe' η)
  rs : (σ : has-section f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ - → (h , -)) q
   where
    q : happly (f ∘ h) id (inverse (happly (f ∘ h) id) (hfe (f ∘ h) id) η) ≡ η
    q = inverse-is-section (happly (f ∘ h) id) (hfe (f ∘ h) id) η
  c : is-singleton (has-section f)
  c = retract-of-singleton (r , s , rs) b
  d : (σ : has-section f) → h , fh ≡ σ
  d = singletons-are-subsingletons (has-section f) c (h , fh)

section-has-at-most-one-retraction : hfunext 𝓤 𝓤 → dfunext 𝓥 𝓤
                                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → has-section f
                                   → is-subsingleton (has-retraction f)
section-has-at-most-one-retraction {𝓤} {𝓥} hfe fe' {X} {Y} f (g , fg) (h , hf) = d
 where
  fe : dfunext 𝓤 𝓤
  fe = hfunext-gives-dfunext hfe
  a : invertible f
  a = joyal-equivs-are-invertible f ((g , fg) , (h , hf))
  b : is-singleton (fiber (λ h →  h ∘ f) id)
  b = invertibles-are-equivs (λ h → h ∘ f) (pre-comp-invertible fe' fe f a) id
  r : fiber (λ h →  h ∘ f) id → has-retraction f
  r (h , p) = (h , happly (h ∘ f) id p)
  s : has-retraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , fe η)
  rs : (σ : has-retraction f) → r (s σ) ≡ σ
  rs (h , η) = ap (λ - → (h , -)) q
   where
    q : happly (h ∘ f) id (inverse (happly (h ∘ f) id) (hfe (h ∘ f) id) η) ≡ η
    q = inverse-is-section (happly (h ∘ f) id) (hfe (h ∘ f) id) η
  c : is-singleton (has-retraction f)
  c = retract-of-singleton (r , s , rs) b
  d : (ρ : has-retraction f) → h , hf ≡ ρ
  d = singletons-are-subsingletons (has-retraction f) c (h , hf)

being-joyal-equiv-is-a-subsingleton : hfunext 𝓤 𝓤 → hfunext 𝓥 𝓥 → dfunext 𝓥 𝓤
                                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                    → (f : X → Y) → is-subsingleton (is-joyal-equiv f)

being-joyal-equiv-is-a-subsingleton fe₀ fe₁ fe₂ f = ×-is-subsingleton'
                                                      (retraction-has-at-most-one-section fe₂ fe₁ f ,
                                                       section-has-at-most-one-retraction fe₀ fe₂ f)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="propositionalextensionality"></a> Propositional extensionality

We have been using the mathematical terminology "subsingleton", but
tradition in the formulation of the next notion demands the logical
terminology "proposition". Propositional extensionality says that any
two logically equivalent propositions are equal:

\begin{code}
propext : ∀ 𝓤  → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q
\end{code}

This is directly implied by univalence:

\begin{code}
univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g =
 Eq-to-Id ua P Q (logically-equivalent-subsingletons-are-equivalent P Q i j (f , g))
\end{code}

For set-level mathematics, function extensionality and propositional
extensionality are often the only consequences of univalence that are
needed. An exception is the theorem that the type of ordinals in a
universe is an ordinal in the next universe, which requires univalence
for sets (see the HoTT Book).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="equivconstructions"></a> Some constructions with types of equivalences

We first prove some
properties of equivalence symmetrization and composition:

\begin{code}
≃-refl-left : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
            → ≃-refl X ● α ≡ α
≃-refl-left fe fe' α = to-Σ-≡ (refl _ , being-equiv-is-a-subsingleton fe fe' _ _ _)

≃-sym-left-inverse : dfunext 𝓥 𝓥
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                   → ≃-sym α ● α ≡ ≃-refl Y
≃-sym-left-inverse fe (f , e) = to-Σ-≡ (p , being-equiv-is-a-subsingleton fe fe _ _ _)
 where
  p : f ∘ inverse f e ≡ id
  p = fe (inverse-is-section f e)

≃-sym-right-inverse : dfunext 𝓤 𝓤
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                    → α ● ≃-sym α ≡ ≃-refl X
≃-sym-right-inverse fe (f , e) = to-Σ-≡ (p , being-equiv-is-a-subsingleton fe fe _ _ _)
 where
  p : inverse f e ∘ f ≡ id
  p = fe (inverse-is-retraction f e)
\end{code}

We then transfer the above to equivalence types:

\begin{code}
≃-Sym : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → (X ≃ Y) ≃ (Y ≃ X)
≃-Sym fe₀ fe₁ fe₂ = invertibility-gives-≃ ≃-sym
                     ( ≃-sym , ≃-sym-involutive fe₀ fe₂ , ≃-sym-involutive fe₁ fe₂)

≃-Comp : dfunext 𝓦 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦) (𝓥 ⊔ 𝓦 ) → dfunext 𝓥 𝓥 → dfunext 𝓦 (𝓤 ⊔ 𝓦)
       → dfunext (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓦 ) → dfunext 𝓤 𝓤
       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ )
       → X ≃ Y → (Y ≃ Z) ≃ (X ≃ Z)
≃-Comp fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Z α = invertibility-gives-≃ (α ●_) ((≃-sym α ●_) , p , q)
 where
  p = λ β → ≃-sym α ● (α ● β) ≡⟨ ●-assoc fe₀ fe₁ (≃-sym α) α β ⟩
            (≃-sym α ● α) ● β ≡⟨ ap (_● β) (≃-sym-left-inverse fe₂ α) ⟩
            ≃-refl _ ● β      ≡⟨ ≃-refl-left fe₀ fe₁ _ ⟩
            β                 ∎

  q = λ γ → α ● (≃-sym α ● γ) ≡⟨ ●-assoc fe₃ fe₄ α (≃-sym α) γ ⟩
            (α ● ≃-sym α) ● γ ≡⟨ ap (_● γ) (≃-sym-right-inverse fe₅ α) ⟩
            ≃-refl _ ● γ      ≡⟨ ≃-refl-left fe₃ fe₄ _ ⟩
            γ                 ∎
\end{code}

Using this we get the following self-congruence property of equivalences:

\begin{code}
Eq-Eq-cong' : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓤
            → dfunext 𝓥 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦) (𝓥 ⊔ 𝓦) → dfunext 𝓦 𝓦
            → dfunext 𝓦 (𝓥 ⊔ 𝓦) → dfunext 𝓥 𝓥 → dfunext 𝓦 (𝓦 ⊔ 𝓣)
            → dfunext (𝓦 ⊔ 𝓣) (𝓦 ⊔ 𝓣) → dfunext 𝓣 𝓣 → dfunext 𝓣 (𝓦 ⊔ 𝓣)
            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
            → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)
Eq-Eq-cong' fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ fe₆ fe₇ fe₈ fe₉ fe₁₀ fe₁₁ {X} {Y} {A} {B} α β =
  (X ≃ Y)  ≃⟨ ≃-Comp fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Y (≃-sym α) ⟩
  (A ≃ Y)  ≃⟨ ≃-Sym fe₃ fe₆ fe₄ ⟩
  (Y ≃ A)  ≃⟨ ≃-Comp fe₆ fe₄ fe₇ fe₈ fe₉ fe₁₀ A (≃-sym β) ⟩
  (B ≃ A)  ≃⟨ ≃-Sym fe₈ fe₁₁ fe₉ ⟩
  (A ≃ B)  ■
\end{code}

The above shows why global function extensionality would be a better
assumption in practice.

\begin{code}
Eq-Eq-cong : global-dfunext
           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
           → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)
Eq-Eq-cong fe = Eq-Eq-cong' fe fe fe fe fe fe fe fe fe fe fe fe
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="embeddings"></a> Type embeddings

A function is called an embedding if its fibers are all
subsingletons. In particular, equivalences are embeddings. However,
sections of types more general than sets [don't need to be
embeddings](https://lmcs.episciences.org/2027).

\begin{code}
is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = (y : codomain f) → is-subsingleton(fiber f y)

being-embedding-is-a-subsingleton : global-dfunext
                                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-subsingleton(is-embedding f)
being-embedding-is-a-subsingleton fe f = Π-is-subsingleton fe
                                          (λ x → being-subsingleton-is-a-subsingleton fe)
\end{code}

For example, if `A` is a subsingleton, then the second projection `A ×
X → X` is an embedding:

\begin{code}
pr₂-embedding : (A : 𝓤 ̇ ) (X : 𝓥 ̇ )
              → is-subsingleton A → is-embedding (λ (z : A × X) → pr₂ z)
pr₂-embedding A X i x ((a , x) , refl x) ((b , x) , refl x) = p
 where
  p : ((a , x) , refl x) ≡ ((b , x) , refl x)
  p = ap (λ - → ((- , x) , refl x)) (i a b)
\end{code}

We can use the following criterion to prove that some maps are embeddings:

\begin{code}
embedding-lemma : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → ((x : X) → is-singleton (fiber f (f x)))
                → is-embedding f
embedding-lemma f φ = γ
 where
  γ : (y : codomain f) (u v : fiber f y) → u ≡ v
  γ y (x , p) v = j (x , p) v
   where
    q : fiber f (f x) ≡ fiber f y
    q = ap (fiber f) p
    i : is-singleton (fiber f y)
    i = transport is-singleton q (φ x)
    j : is-subsingleton (fiber f y)
    j = singletons-are-subsingletons (fiber f y) i

embedding-criterion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → ((x x' : X) → (f x ≡ f x') ≃ (x ≡ x'))
                    → is-embedding f
embedding-criterion f e = embedding-lemma f b
 where
  X = domain f
  a : (x : X) → (Σ \(x' : X) → f x' ≡ f x) ≃ (Σ \(x' : X) → x' ≡ x)
  a x = Σ-cong (λ x' → e x' x)
  a' : (x : X) → fiber f (f x) ≃ singleton-type x
  a' = a
  b : (x : X) → is-singleton (fiber f (f x))
  b x = equiv-to-singleton (a' x) (singleton-types-are-singletons X x)
\end{code}

An equivalent formulation of `f` being an embedding is that the map

   > `ap f {x} {x'} : x ≡ x' → f x ≡ f x'`

is an equivalence for all `x x' : X`.

\begin{code}
ap-is-equiv-gives-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → ((x x' : X) → is-equiv (ap f {x} {x'}))
                            → is-embedding f
ap-is-equiv-gives-embedding f i = embedding-criterion f
                                   (λ x' x → ≃-sym (ap f {x'} {x} , (i x' x)))

embedding-gives-ap-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-embedding f
                            → (x x' : X) → is-equiv (ap f {x} {x'})
embedding-gives-ap-is-equiv {𝓤} {𝓥} {X} f e = γ
 where
  d : (x' : X) → (Σ \(x : X) → f x' ≡ f x) ≃ (Σ \(x : X) → f x ≡ f x')
  d x' = Σ-cong (λ x → ⁻¹-≃ (f x') (f x))
  s : (x' : X) → is-subsingleton (Σ \(x : X) → f x' ≡ f x)
  s x' = equiv-to-subsingleton (d x') (e (f x'))
  γ : (x x' : X) → is-equiv (ap f {x} {x'})
  γ x = subsingleton-equiv-lemma x (λ x' → ap f {x} {x'}) (s x)

embedding-criterion-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-embedding f
                             → ((x' x : X) → (f x' ≡ f x) ≃ (x' ≡ x))
embedding-criterion-converse f e x' x = ≃-sym (ap f {x'} {x} ,
                                               embedding-gives-ap-is-equiv f e x' x)
\end{code}

Hence embeddings of arbitrary types are left cancellable, but the
converse fails in general.

*Exercise.* Left cancellable maps into *sets* are always embeddings.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="yoneda"></a> The Yoneda Lemma for types

As we [have seen](HoTT-UF-Agda.html#identitytypeuf), a type `X` can be
seen as an `∞`-groupoid and hence as an `∞`-category, with
identifications as the arrows. Likewise
a universe `𝓤` can be seen as the ∞-generalization of the category of
sets, with functions as the arrows. Hence a type family

   > `A : X → 𝓤`

can be seen as an `∞-`presheaf, because groupoids are self-dual
categories.

With this view, the identity type former `Id X : X → X → 𝓤` plays the role
of the [Yoneda embedding](https://ncatlab.org/nlab/show/Yoneda+embedding):

\begin{code}
𝓨 : {X : 𝓤 ̇ } → X → (X → 𝓤 ̇ )
𝓨 {𝓤} {X} = Id X
\end{code}

By our definition of [`Nat`](HoTT-UF-Agda.html#Nat), for any `A : X → 𝓥 ̇ ` and `x : X` we have

   > `Nat (𝓨 x) A = (y : X) → x ≡ y → A y`,

and, by [`Nats-are-natural`](HoTT-UF-Agda.html#Nats-are-natural), we have
that `Nat (𝓨 x) A` is the type of natural transformations from the
presheaf `𝓨 x` to the presheaf `A`.

The starting point of the Yoneda Lemma, in our context, is that every natural transformation
`Nat (𝓨 x) A` is a transport:

\begin{code}
transport-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                → (τ : Nat (𝓨 x) A)
                → (y : X) (p : x ≡ y) → τ y p ≡ transport A p (τ x (refl x))
transport-lemma A x τ x (refl x) = refl (τ x (refl x))
\end{code}

We refer to `τ x (refl x)` as the *Yoneda element* of `τ` and denote it by
`𝓔 A x τ`.

\begin{code}
𝓔 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
  → Nat (𝓨 x) A → A x
𝓔 A x τ = τ x (refl x)
\end{code}

The function

   > `𝓔 A x : Nat (𝓨 x) A → A x`

is an equivalence with
inverse

   > `𝓝 A x : A x → Nat (𝓨 x) A`,

the transport natural transformation induced by `A` and `x`:

\begin{code}
𝓝 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
  → A x → Nat (𝓨 x) A
𝓝 A x a y p = transport A p a

yoneda-η : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
         → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
         → 𝓝 A x ∘ 𝓔 A x ∼ id
yoneda-η fe fe' A x = γ
 where
  γ : (τ : Nat (𝓨 x) A) → (λ y p → transport A p (τ x (refl x))) ≡ τ
  γ τ = fe (λ y → fe' (λ p → (transport-lemma A x τ y p)⁻¹))

yoneda-ε : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
         → 𝓔 A x ∘ 𝓝 A x ∼ id
yoneda-ε A x = γ
 where
  γ : (a : A x) → transport A (refl x) a ≡ a
  γ = refl
\end{code}

By a fiberwise equivalence we mean a natural transformation whose
components are all equivalences:

\begin{code}
is-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                   → Nat A B → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
is-fiberwise-equiv τ = ∀ x → is-equiv (τ x)

𝓔-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
           → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
           → is-fiberwise-equiv (𝓔 A)
𝓔-is-equiv fe fe' A x = invertibles-are-equivs (𝓔 A x ) (𝓝 A x , yoneda-η fe fe' A x , yoneda-ε A x)

𝓝-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
           → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
           → is-fiberwise-equiv (𝓝 A)
𝓝-is-equiv fe fe' A x = invertibles-are-equivs (𝓝 A x) (𝓔 A x , yoneda-ε A x , yoneda-η fe fe' A x)
\end{code}

This gives the [Yoneda Lemma for
types](https://homotopytypetheory.org/2012/05/02/a-type-theoretical-yoneda-lemma/),
which says that natural transformations from `𝓨 x` to `A` are in
canonical bijection with elements of `A x`:

\begin{code}
Yoneda-Lemma : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
             → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
             → Nat (𝓨 x) A ≃ A x
Yoneda-Lemma fe fe' A x = 𝓔 A x , 𝓔-is-equiv fe fe' A x
\end{code}

A [universal element of a
presheaf](https://en.wikipedia.org/wiki/Representable_functor#Universal_elements) `A`
corresponds in our context to an element of the type `is-singleton (Σ A)`.

If the transport transformation is a fiberwise equivalence,
then `A` has a universal element. More generally, we have the following:

\begin{code}
retract-universal-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                        → ((y : X) → A y ◁ (x ≡ y))
                        → is-singleton (Σ A)
retract-universal-lemma A x ρ = i
 where
  σ : Σ A ◁ singleton-type' x
  σ = Σ-retract ρ
  i : is-singleton (Σ A)
  i = retract-of-singleton σ (singleton-types'-are-singletons (domain A) x)

fiberwise-equiv-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) (a : A x)
                          → is-fiberwise-equiv (𝓝 A x a)
                          → is-singleton (Σ A)
fiberwise-equiv-universal A x a e = retract-universal-lemma A x ρ
 where
  ρ : ∀ y → A y ◁ (x ≡ y)
  ρ y = ≃-gives-▷ (𝓝 A x a y , e y)
\end{code}

A presheaf is called *representable* if it is pointwise equivalent to a
presheaf of the form `𝓨 x`:

\begin{code}
_≃̇_ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ≃̇ B = ∀ x → A x ≃ B x

is-representable : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-representable A = Σ \(x : domain A) → 𝓨 x ≃̇ A

representable-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                        → is-representable A
                        → is-singleton (Σ A)
representable-universal A (x , e) = retract-universal-lemma A x (λ x → ≃-gives-▷ (e x))

universal-fiberwise-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                          → is-singleton (Σ A)
                          → (τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ
universal-fiberwise-equiv {𝓤} {𝓥} {X} A x u τ = γ
 where
  g : singleton-type' x → Σ A
  g = NatΣ τ
  e : is-equiv g
  e = maps-of-singletons-are-equivs g (singleton-types'-are-singletons X x) u
  γ : is-fiberwise-equiv τ
  γ = NatΣ-equiv-gives-fiberwise-equiv τ e

universal-representable : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → is-singleton (Σ A)
                        → is-representable A
universal-representable {𝓤} {𝓥} {X} {A} ((x , a) , p) = x , φ
 where
  e : is-fiberwise-equiv (𝓝 A x a)
  e = universal-fiberwise-equiv A x ((x , a) , p) (𝓝 A x a)
  φ : (y : X) → (x ≡ y) ≃ A y
  φ y = (𝓝 A x a y , e y)
\end{code}

Combining `retract-universal-lemma` and `universal-fiberwise-equiv` we get the
[following](https://github.com/HoTT/book/issues/718#issuecomment-65378867):

\begin{code}
fiberwise-retractions-are-equivs : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                                 → (τ : Nat (𝓨 x) A)
                                 → ((y : X) → has-section (τ y))
                                 → is-fiberwise-equiv τ
fiberwise-retractions-are-equivs {𝓤} {𝓥} {X} A x τ s = γ
 where
  ρ : (y : X) → A y ◁ (x ≡ y)
  ρ y = τ y , s y
  i : is-singleton (Σ A)
  i = retract-universal-lemma A x ρ
  γ : is-fiberwise-equiv τ
  γ = universal-fiberwise-equiv A x i τ
\end{code}

Perhaps the following formulation is more appealing:

\begin{code}
fiberwise-◁-gives-≃ : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (x : X)
                    → ((y : X) → A y ◁ (x ≡ y))
                    → ((y : X) → A y ≃ (x ≡ y))
fiberwise-◁-gives-≃ X A x ρ = γ
 where
  f : (y : X) → (x ≡ y) → A y
  f y = retraction (ρ y)
  e : is-fiberwise-equiv f
  e = fiberwise-retractions-are-equivs A x f (λ y → retraction-has-section (ρ y))
  γ : (y : X) → A y ≃ (x ≡ y)
  γ y = ≃-sym(f y , e y)
\end{code}

To prove that [`𝓨 {𝓤} {X}` is an embedding](https://arxiv.org/abs/1903.01211) of `X` into `X → 𝓤` for any
type `X : 𝓤`, we need the following two lemmas, which are interesting on their own right:

\begin{code}
being-fiberwise-equiv-is-a-subsingleton : global-dfunext
                                        → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                        → (τ : Nat A B)
                                        → is-subsingleton (is-fiberwise-equiv τ)
being-fiberwise-equiv-is-a-subsingleton fe τ = Π-is-subsingleton fe
                                                (λ y → being-equiv-is-a-subsingleton fe fe (τ y))

being-representable-is-a-subsingleton : global-dfunext
                                      → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                                      → is-subsingleton (is-representable A)
being-representable-is-a-subsingleton fe {X} A r₀ r₁ = γ
 where
  u : is-singleton (Σ A)
  u = representable-universal A r₀
  i : (x : X) (τ : Nat (𝓨 x) A) → is-singleton (is-fiberwise-equiv τ)
  i x τ = pointed-subsingletons-are-singletons
           (is-fiberwise-equiv τ)
           (universal-fiberwise-equiv A x u τ)
           (being-fiberwise-equiv-is-a-subsingleton fe τ)
  ε : (x : X) → (𝓨 x ≃̇ A) ≃ A x
  ε x = ((y : X) → 𝓨 x y ≃ A y)                       ≃⟨ ΠΣ-distr-≃ ⟩
        (Σ \(τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ) ≃⟨ pr₁ , pr₁-equiv (Nat (𝓨 x) A) is-fiberwise-equiv (i x) ⟩
        Nat (𝓨 x) A                                   ≃⟨ Yoneda-Lemma fe fe A x ⟩
        A x                                           ■
  δ : is-representable A ≃ Σ A
  δ = Σ-cong ε
  v : is-singleton (is-representable A)
  v = equiv-to-singleton δ u
  γ : r₀ ≡ r₁
  γ = singletons-are-subsingletons (is-representable A) v r₀ r₁
\end{code}

With this it is almost immediate that the Yoneda map is an embedding:

\begin{code}
𝓨-embedding : Univalence → (X : 𝓤 ̇ ) → is-embedding (𝓨 {𝓤} {X})
𝓨-embedding {𝓤} ua X A = γ
 where
  hfe : global-hfunext
  hfe = univalence-gives-global-hfunext ua
  dfe : global-dfunext
  dfe = univalence-gives-global-dfunext ua
  e : fiber 𝓨 A ≃ is-representable A
  e = Σ-cong (λ x → (𝓨 x ≡ A)                 ≃⟨ (happly (𝓨 x) A) , hfe (𝓨 x) A ⟩
                    ((y : X) → 𝓨 x y ≡ A y)   ≃⟨ Π-cong dfe dfe X
                                                   (λ y → 𝓨 x y ≡ A y)
                                                   (λ y → 𝓨 x y ≃ A y)
                                                   (λ y → is-univalent-≃ (ua 𝓤) (𝓨 x y) (A y)) ⟩
                    ((y : X) → 𝓨 x y ≃ A y)   ■)
  γ : is-subsingleton (fiber 𝓨 A)
  γ = equiv-to-subsingleton e (being-representable-is-a-subsingleton dfe A)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="universelifting"></a> Universe lifting

Universes are not cumulative on the nose in Agda, in the sense that
from `X : 𝓤` we would get `X : 𝓤⁺` or `X : 𝓤 ⊔ 𝓥`.  Instead we work
with embeddings of universes into larger universes.

The following together with its induction principle should be
considered as part of the universe handling of our spartan Martin-Löf
type theory:

\begin{code}
record Lift {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 constructor
  lift
 field
  lower : X

open Lift public

Lift-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇ ) (A : Lift 𝓥 X → 𝓦 ̇ )
               → ((x : X) → A (lift x))
               → (l : Lift 𝓥 X) → A l
Lift-induction 𝓥 X A φ (lift x) = φ x

Lift-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } {B : 𝓦 ̇ }
               → (X → B) → Lift 𝓥 X → B
Lift-recursion 𝓥 {X} {B} = Lift-induction 𝓥 X (λ _ → B)
\end{code}

This gives an equivalence `lift : X → Lift 𝓥 X` and hence an embedding
`Lift 𝓥 : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇`. The following two constructions can be
performed with induction, but actually hold on the nose by the [η rule
for records](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion):

\begin{code}
lower-lift : {X : 𝓤 ̇ } (x : X) → lower {𝓤} {𝓥} (lift x) ≡ x
lower-lift = refl

lift-lower : {X : 𝓤 ̇ } (l : Lift 𝓥 X) → lift (lower l) ≡ l
lift-lower = refl

Lift-≃ : (X : 𝓤 ̇ ) → Lift 𝓥 X ≃ X
Lift-≃ {𝓤} {𝓥} X = invertibility-gives-≃ lower (lift , lift-lower , lower-lift {𝓤} {𝓥})

≃-Lift : (X : 𝓤 ̇ ) → X ≃ Lift 𝓥 X
≃-Lift {𝓤} {𝓥} X = invertibility-gives-≃ lift (lower , lower-lift {𝓤} {𝓥} , lift-lower)
\end{code}

With universe lifting, we can generalize equivalence induction as
follows, in several steps.

Firstly, function extensionality for a pair of universes gives
function extensionality for any pair of lower universes:

\begin{code}
lower-dfunext : ∀ 𝓦 𝓣 𝓤 𝓥 → dfunext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → dfunext 𝓤 𝓥
lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe {X} {A} {f} {g} h = p
 where
  A' : Lift 𝓦 X → 𝓥 ⊔ 𝓣 ̇
  A' y = Lift 𝓣 (A (lower y))
  f' g' : Π A'
  f' y = lift (f (lower y))
  g' y = lift (g (lower y))
  h' : f' ∼ g'
  h' y = ap lift (h (lower y))
  p' : f' ≡ g'
  p' = fe h'
  p : f ≡ g
  p = ap (λ f' x → lower (f' (lift x))) p'
\end{code}

Secondly, a function from a universe to a higher universe is an
embedding provided it maps any type to an equivalent type and the two
universes are univalent:

\begin{code}
universe-embedding-criterion : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥)
                             → (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
                             → ((X : 𝓤 ̇ ) → f X ≃ X)
                             → is-embedding f
universe-embedding-criterion {𝓤} {𝓥} ua ua' f i = embedding-criterion f γ
 where
  fe : dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext ua'
  fe₀ : dfunext 𝓤 𝓤
  fe₀ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe
  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext 𝓥 𝓥 𝓤 (𝓤 ⊔ 𝓥) fe
  γ : (X X' : 𝓤 ̇ ) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' =  (f X ≡ f X')  ≃⟨ is-univalent-≃ ua' (f X) (f X') ⟩
            (f X ≃ f X')  ≃⟨ Eq-Eq-cong' fe fe fe fe fe fe₀ fe₁ fe fe₀ fe₀ fe₀ fe₀ (i X) (i X') ⟩
            (X ≃ X')      ≃⟨ ≃-sym (is-univalent-≃ ua X X') ⟩
            (X ≡ X')      ■
\end{code}

In particular, the function `Lift` is an embedding:

\begin{code}
Lift-is-embedding : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → is-embedding (Lift {𝓤} 𝓥)
Lift-is-embedding {𝓤} {𝓥} ua ua' = universe-embedding-criterion {𝓤} {𝓥} ua ua' (Lift 𝓥) Lift-≃
\end{code}

Thirdly, we have a generalization of `univalence→`
from a single universe to a pair of universes. We work with two
symmetrical versions, where the second is derived from the first. Here
an anonymous module is used to provide the same hypotheses to both
versions:

\begin{code}
module _ {𝓤 𝓥 : Universe}
         (ua : is-univalent 𝓥)
         (ua' : is-univalent (𝓤 ⊔ 𝓥))
 where

 private
  fe : dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext ua'
  fe₀ : dfunext 𝓥 (𝓤 ⊔ 𝓥)
  fe₀ = lower-dfunext 𝓤 𝓤 𝓥 (𝓤 ⊔ 𝓥) fe
  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext (𝓤 ⊔ 𝓥) 𝓤 𝓤 (𝓤 ⊔ 𝓥) fe
  fe₂ : dfunext 𝓥 𝓥
  fe₂ = lower-dfunext 𝓤 𝓤 𝓥 𝓥 fe
  fe₃ : dfunext 𝓤 𝓤
  fe₃ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe

 univalence→' : (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓥 ̇ ) → X ≃ Y)
 univalence→' X = s
  where
   abstract
     e : (Y : 𝓥 ̇ ) → (X ≃ Y) ≃ (Lift 𝓤 Y ≡ Lift 𝓥 X)
     e Y = (X ≃ Y)                ≃⟨ ≃-Sym fe₀ fe₁ fe ⟩
           (Y ≃ X)                ≃⟨ Eq-Eq-cong' fe₁ fe fe₂ fe₁ fe fe fe fe₃ fe fe fe fe (≃-Lift Y) (≃-Lift X) ⟩
           (Lift 𝓤 Y ≃ Lift 𝓥 X) ≃⟨ ≃-sym (is-univalent-≃ ua' (Lift 𝓤 Y) (Lift 𝓥 X)) ⟩
           (Lift 𝓤 Y ≡ Lift 𝓥 X) ■
     d : (Σ \(Y : 𝓥 ̇ ) → X ≃ Y) ≃ (Σ \(Y : 𝓥 ̇ ) → Lift 𝓤 Y ≡ Lift 𝓥 X)
     d = Σ-cong e
     i : is-subsingleton (Σ \(Y : 𝓥 ̇ ) → Lift 𝓤 Y ≡ Lift 𝓥 X)
     i = Lift-is-embedding ua ua' (Lift 𝓥 X)
     s : is-subsingleton (Σ \(Y : 𝓥 ̇ ) → X ≃ Y)
     s = equiv-to-subsingleton d i

 univalence→'-dual : (Y : 𝓤 ̇ ) → is-subsingleton (Σ \(X : 𝓥 ̇ ) → X ≃ Y)
 univalence→'-dual Y = equiv-to-subsingleton e i
  where
   e : (Σ \(X : 𝓥 ̇ ) → X ≃ Y) ≃ (Σ \(X : 𝓥 ̇ ) → Y ≃ X)
   e = Σ-cong (λ X → ≃-Sym fe₁ fe₀ fe)
   i : is-subsingleton (Σ \(X : 𝓥 ̇ ) → Y ≃ X)
   i = univalence→' Y
\end{code}

This is the end of the anonymous module. We are interested in these corollaries:

\begin{code}
univalence→'' : is-univalent (𝓤 ⊔ 𝓥) → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
univalence→'' ua = univalence→' ua ua

univalence→''-dual : is-univalent (𝓤 ⊔ 𝓥) → (Y : 𝓤 ̇ ) → is-subsingleton (Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
univalence→''-dual ua = univalence→'-dual ua ua
\end{code}

The first one is applied to get the following, where `Y` lives in a
universe above that of `X`:

\begin{code}
H↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → A (Lift 𝓥 X) (≃-Lift X) → (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A Y e
H↑-≃ {𝓤} {𝓥} {𝓦} ua X A a Y e = τ a
 where
  B : (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y) → 𝓦 ̇
  B (Y , e) = A Y e
  t : Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y
  t = (Lift 𝓥 X , ≃-Lift X)
  p : t ≡ (Y , e)
  p = univalence→'' {𝓤} {𝓥} ua X t (Y , e)
  τ : B t → B (Y , e)
  τ = transport B p
\end{code}

The difference with `H-≃` is that here, to get the conclusion, we need
to assume

   > `A (Lift 𝓥 X) (≃-Lift X)`

rather than

   > `A X (≃-refl)`.

The analogous equation is satisfied by `H↑-≃`:

\begin{code}
H↑-≃-equation : (ua : is-univalent (𝓤 ⊔ 𝓥))
              → (X : 𝓤 ̇ )
              → (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
              → (a : A (Lift 𝓥 X) (≃-Lift X))
              → H↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ≡ a
H↑-≃-equation {𝓤} {𝓥} {𝓦} ua X A a =
  H↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X)  ≡⟨ refl _ ⟩
  transport B p a                      ≡⟨ ap (λ - → transport B - a) q ⟩
  transport B (refl t) a               ≡⟨ refl _ ⟩
  a                                    ∎
 where
  B : (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y) → 𝓦 ̇
  B (Y , e) = A Y e
  t : Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y
  t = (Lift 𝓥 X , ≃-Lift X)
  p : t ≡ t
  p = univalence→'' {𝓤} {𝓥} ua X t t
  q : p ≡ refl t
  q = subsingletons-are-sets (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
       (univalence→'' {𝓤} {𝓥} ua X) t t p (refl t)
\end{code}

And we have a similar development with a similar example:

\begin{code}
J↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓥 ̇ )
     → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) (≃-Lift X))
     → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A X Y e
J↑-≃ ua A φ X = H↑-≃ ua X (A X) (φ X)

H↑-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
         → A (Lift 𝓥 X) lift → (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → is-equiv f → A Y f
H↑-equiv {𝓤} {𝓥} {𝓦} ua X A a Y f i = γ (f , i) i
 where
  B : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  B Y (f , i) = is-equiv f → A Y f
  b : B (Lift 𝓥 X) (≃-Lift X)
  b = λ (_ : is-equiv lift) → a
  γ : (e : X ≃ Y) → B Y e
  γ = H↑-≃ ua X B b Y

J↑-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
         → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) lift)
         → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → is-equiv f → A X Y f
J↑-equiv ua A φ X = H↑-equiv ua X (A X) (φ X)
\end{code}

All invertible functions from a type in a universe `𝓤` to a type in a
higher universe `𝓤 ⊔ 𝓥` satisfy a given property if (and only if) the functions


   > `lift {𝓤} {𝓥} {X} : X → Lift 𝓥 X`

satisfy the property for all `X : 𝓤` (where we don't write the
implicit arguments for `lift`):

\begin{code}
J↑-invertible : is-univalent (𝓤 ⊔ 𝓥)
              → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
              → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) lift)
              → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → invertible f → A X Y f
J↑-invertible ua A φ X Y f i = J↑-equiv ua A φ X Y f (invertibles-are-equivs f i)
\end{code}

Here is an example. First, `lift` is a half adjoint equivalence on the nose:

\begin{code}
lift-is-hae : (X : 𝓤 ̇ ) → is-hae {𝓤} {𝓤 ⊔ 𝓥} {X} {Lift 𝓥 X} (lift {𝓤} {𝓥})
lift-is-hae {𝓤} {𝓥} X = lower , lower-lift {𝓤} {𝓥} , lift-lower , λ x → refl (refl (lift x))
\end{code}

Hence all invertible maps going up universe levels are half adjoint
equivalences:

\begin{code}
equivs-are-haes↑ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ̇ } {Y : 𝓤 ⊔ 𝓥 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f
equivs-are-haes↑ {𝓤} {𝓥} ua {X} {Y} = J↑-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f) lift-is-hae X Y
\end{code}

We have a dual development with the universes going down, where we
consider `lower` in place of `lift`:

\begin{code}
H↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (Y : 𝓤 ̇ ) (A : (X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → A (Lift 𝓥 Y) (Lift-≃ Y) → (X : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A X e
H↓-≃ {𝓤} {𝓥} {𝓦} ua Y A a X e = τ a
 where
  B : (Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y) → 𝓦 ̇
  B (X , e) = A X e
  t : Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y
  t = (Lift 𝓥 Y , Lift-≃ Y)
  p : t ≡ (X , e)
  p = univalence→'-dual ua ua Y t (X , e)
  τ : B t → B (X , e)
  τ = transport B p

J↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y (Lift-≃ Y))
     → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e
J↓-≃ ua A φ X Y = H↓-≃ ua Y (λ X → A X Y) (φ Y) X

H↓-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (Y : 𝓤 ̇ ) (A : (X : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
         → A (Lift 𝓥 Y) lower → (X : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → is-equiv f → A X f
H↓-equiv {𝓤} {𝓥} {𝓦} ua Y A a X f i = γ (f , i) i
 where
  B : (X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  B X (f , i) = is-equiv f → A X f
  b : B (Lift 𝓥 Y) (Lift-≃ Y)
  b = λ (_ : is-equiv lower) → a
  γ : (e : X ≃ Y) → B X e
  γ = H↓-≃ ua Y B b X

J↓-equiv : is-univalent (𝓤 ⊔ 𝓥)
         → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → (X → Y) → 𝓦 ̇ )
         → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y lower)
         → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A X Y f
J↓-equiv ua A φ X Y = H↓-equiv ua Y (λ X → A X Y) (φ Y) X
\end{code}

All invertible functions from a type in a universe `𝓤 ⊔ 𝓥` to a type in the
lower universe `𝓤` satisfy a given property if (and only if) the functions

   > `lower {𝓤} {𝓥} {Y} : Lift 𝓥 Y → Y`

satisfy the property for all `Y : 𝓤`:

\begin{code}
J↓-invertible : is-univalent (𝓤 ⊔ 𝓥)
              → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → (X → Y) → 𝓦 ̇ )
              → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y lower)
              → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (f : X → Y) → invertible f → A X Y f
J↓-invertible ua A φ X Y f i = J↓-equiv ua A φ X Y f (invertibles-are-equivs f i)
\end{code}

And we have similar examples:

\begin{code}
lower-is-hae : (X : 𝓤 ̇ ) → is-hae (lower {𝓤} {𝓥} {X})
lower-is-hae {𝓤} {𝓥} X = lift , lift-lower , lower-lift {𝓤} {𝓥} , (λ x → refl (refl (lower x)))

equivs-are-haes↓ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ⊔ 𝓥 ̇ } {Y : 𝓤 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f
equivs-are-haes↓ {𝓤} {𝓥} ua {X} {Y} = J↓-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f) lower-is-hae X Y
\end{code}

A crucial example of an equivalence "going down one universe" is
`Id-to-Eq X Y`. This is because the identity type `X ≡ Y` lives in the
successor universe `𝓤 ⁺` if `X` and `Y` live in `𝓤`, whereas the
equivalence type `X ≃ Y` lives in the same universe as `X` and
`Y`. Hence we can apply `invertibles-are-haes↓` to `Id-to-Eq X Y` to
conclude that it is a half adjoint equivalence:

\begin{code}
Id-to-Eq-is-hae : is-univalent 𝓤 → is-univalent (𝓤 ⁺)
                → {X Y : 𝓤 ̇ } → is-hae (Id-to-Eq X Y)
Id-to-Eq-is-hae ua ua⁺ {X} {Y} = equivs-are-haes↓ ua⁺ (Id-to-Eq X Y) (ua X Y)
\end{code}

We apply the fact that `Id-to-Eq X Y` is a half adjoint equivalence to
get a simple proof that [Magma identity coincides with Magma
equivalence](HoTT-UF-Agda.html#magmaequivalences) (and hence with
Magma isomorphism).

The remainder of this section is not used anywhere else.  Using the
universe `𝓤ω` discussed above, we can consider global properties:

\begin{code}
global-property-of-types : 𝓤ω
global-property-of-types = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
\end{code}

We have already considered a few global properties, in fact,
such as `is-singleton`, `is-subsingleton`, `is-set` and `_is-of-hlevel n`.

We may hope to have that if `A` is a global property of types, then,
in the presence of univalence, for any `X : 𝓤` and `Y : 𝓥`, if `A X` holds
then so does `A Y`.  However, because we have a type of universes, or
universe levels, we may define e.g. `A {𝓤} X = (𝓤 ≡ 𝓤₀)`, which violates
this hope. To get this conclusion, we need an assumption on `A`. We
say that `A` is cumulative if it is preserved by the embedding `Lift`
of universes into higher universes:

\begin{code}
cumulative : global-property-of-types → 𝓤ω
cumulative A = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X)
\end{code}

We can prove the following:

\begin{code}
global-≃-ap : Univalence
            → (A : global-property-of-types)
            → cumulative A
            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y
\end{code}

However, the above notion of global property is very restrictive. For
example, `is-inhabited` defined [below](HoTT-UF-Agda.html#truncation) is a global property of type
`{𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⁺ ̇ `.
Hence we prove something more general, where in this example we take `F 𝓤 = 𝓤 ⁺`.

\begin{code}
global-≃-ap' : Univalence
             → (F : Universe → Universe)
             → (A : {𝓤 : Universe} → 𝓤 ̇ → (F 𝓤) ̇ )
             → ({𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X))
             → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y
global-≃-ap' {𝓤} {𝓥} ua F A φ X Y e =
  A X          ≃⟨ φ X ⟩
  A (Lift 𝓥 X) ≃⟨ Id-to-Eq (A (Lift 𝓥 X)) (A (Lift 𝓤 Y)) q ⟩
  A (Lift 𝓤 Y) ≃⟨ ≃-sym (φ Y) ⟩
  A Y          ■
 where
  d : Lift 𝓥 X ≃ Lift 𝓤 Y
  d = Lift 𝓥 X ≃⟨ Lift-≃ X ⟩
      X        ≃⟨ e ⟩
      Y        ≃⟨ ≃-sym (Lift-≃ Y) ⟩
      Lift 𝓤 Y ■
  p : Lift 𝓥 X ≡ Lift 𝓤 Y
  p = Eq-to-Id (ua (𝓤 ⊔ 𝓥)) (Lift 𝓥 X) (Lift 𝓤 Y) d
  q : A (Lift 𝓥 X) ≡ A (Lift 𝓤 Y)
  q = ap A p
\end{code}

The first claim follows with `F = id`:

\begin{code}
global-≃-ap ua = global-≃-ap' ua id
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="subtypeclassifier"></a> The subtype classifier and other classifiers

We first define the type of embeddings of a type `X` into a type `Y`:

\begin{code}
_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ \(f : X → Y) → is-embedding f
\end{code}

A subtype of a type `Y` is a type `X` *together* with an embedding of `X` into `Y`:

\begin{code}
subtypes-of : 𝓤 ̇ → 𝓤 ⁺ ̇
subtypes-of {𝓤} Y = Σ \(X : 𝓤 ̇ ) → X ↪ Y
\end{code}

We then define the type `Ω 𝓤` of subsingletons in a given universe `𝓤`, which lives in the next universe:

\begin{code}
Ω : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω 𝓤 = Σ \(P : 𝓤 ̇ ) → is-subsingleton P
\end{code}

This type is the subtype classifier of types in `𝓤`, in the sense that
we have a canonical equivalence

   > `subtypes-of Y ≃ (Y → Ω 𝓤)`

for any type `Y : 𝓤`.

*Exercise* (Not easy.) Assume univalence. (0) show
 that `Ω 𝓤` is a set. (1) Conclude that the type `Y → Ω
 𝓤` is a set (even if `Y` is not), which justifies the name powerset for it, and the notation `𝓟 Y`. (2) For `A : 𝓟 Y` and `y : Y` write `y ∈ A` to mean `pr₁(A y)`. Define `A ⊆ B` to mean `(y : Y) → y ∈ A → y ∈ B`. Show that both `∈` and `⊆` are subsingleton-valued relations. (3) Show that `A ≡ B` and `(A ⊆ B) × (B ⊆ A)` are logically equivalent propositions. Thus, univalence gives extensionality for the powerset.

We will derive the claim `subtypes-of Y ≃ (Y → Ω 𝓤)` from something
more general.  We defined embeddings to be maps whose fibers are
all subsingletons. We can replace `is-subsingleton` by an arbitrary
property of — or even structure on — types, which we will name `blue`.
The following generalizes the notion of embedding (when `blue`
means `is-subsingleton`) and equivalence (when `blue` means
`is-singleton`):

\begin{code}
_has_fibers : {X Y : 𝓤 ̇ } → (X → Y) → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
f has blue fibers = ∀ y → blue (fiber f y)
\end{code}

The following generalizes the [slice constructor](HoTT-UF-Agda.html#typeclassifier) `_/_`:

\begin{code}
_/[_]_ : (𝓤 : Universe) → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 /[ blue ] Y = Σ \(X : 𝓤 ̇ ) → Σ \(f : X → Y) → f has blue fibers
\end{code}

We now work with a submodule with hypotheses to generalize the fact
that the [universe is the map
classifier](HoTT-UF-Agda.html#typeclassifier) (when `blue = λ _ → 𝟙`),
using the fact that it is the map classifier in order to perform the
generalization:

\begin{code}
module blue-map-classifier
        (𝓤 𝓥 : Universe)
        (ua : is-univalent 𝓤)
        (ua⁺ : is-univalent (𝓤 ⁺))
        (fe : dfunext 𝓤 (𝓤 ⁺))
        (Y : 𝓤 ̇ )
        (blue : 𝓤 ̇ → 𝓥 ̇ )
       where

 open map-classifier 𝓤 ua fe Y

 χ-is-hae : is-hae χ
 χ-is-hae = equivs-are-haes ua⁺ χ χ-is-equiv
\end{code}

We collect the `blue` types in a type `Blue`:

\begin{code}
 Blue : 𝓤 ⁺ ⊔ 𝓥 ̇
 Blue = Σ blue
\end{code}

Then `Blue` is the classifier of maps with `blue` fibers:

\begin{code}
 bijection : 𝓤 /[ blue ] Y ≃ (Y → Blue)
 bijection = ≃-sym (
  (Y → Blue)                                  ≃⟨ ΠΣ-distr-≃ ⟩
  (Σ \(A : Y → 𝓤 ̇ ) → (y : Y) → blue (A y))   ≃⟨ Σ-change-of-variables-hae (λ A → Π (blue ∘ A)) χ χ-is-hae ⟩
  (Σ \(σ : 𝓤 / Y) → (y : Y) → blue (χ σ y))   ≃⟨ Σ-assoc ⟩
  (𝓤 /[ blue ] Y)                             ■)
\end{code}

This concludes the submodule. In particular, considering `blue =
is-subsingleton`, we get the promised fact that `Ω` is the subtype
classifier:

\begin{code}
Ω-is-subtype-classifier : Univalence → (Y : 𝓤 ̇ ) → subtypes-of Y ≃ (Y → Ω 𝓤)
Ω-is-subtype-classifier {𝓤} ua Y = blue-map-classifier.bijection 𝓤 𝓤 (ua 𝓤) (ua (𝓤 ⁺))
                                     (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺))) Y is-subsingleton
\end{code}

We now consider `blue = is-singleton` and the type of singletons:

\begin{code}
𝓢 : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓢 𝓤 = Σ \(S : 𝓤 ̇ ) → is-singleton S

equiv-classification : Univalence → (Y : 𝓤 ̇ ) → (Σ \(X : 𝓤 ̇ ) → X ≃ Y) ≃ (Y → 𝓢 𝓤)
equiv-classification {𝓤} ua Y = blue-map-classifier.bijection 𝓤 𝓤 (ua 𝓤) (ua (𝓤 ⁺))
                                  (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺))) Y is-singleton
\end{code}

With this we can derive a [fact we already know](HoTT-UF-Agda.html#unicharac), as follows.
First the type of singletons (in a universe) is itself a singleton (in the next universe):

\begin{code}
the-singletons-form-a-singleton : propext 𝓤 → dfunext 𝓤 𝓤 → is-singleton (𝓢 𝓤)
the-singletons-form-a-singleton {𝓤} pe fe = c , φ
 where
  i : is-singleton (Lift 𝓤 𝟙)
  i = equiv-to-singleton (Lift-≃ 𝟙) 𝟙-is-singleton
  c : 𝓢 𝓤
  c = Lift 𝓤 𝟙 , i
  φ : (x : 𝓢 𝓤) → c ≡ x
  φ (S , s) = to-Σ-≡ (p , being-singleton-is-a-subsingleton fe _ _)
   where
    p : Lift 𝓤 𝟙 ≡ S
    p = pe (singletons-are-subsingletons (Lift 𝓤 𝟙) i) (singletons-are-subsingletons S s)
           (λ _ → center S s) (λ _ → center (Lift 𝓤 𝟙) i)
\end{code}

What we already knew is this:

\begin{code}
corollary : Univalence → (Y : 𝓤 ̇ ) → is-singleton (Σ \(X : 𝓤 ̇ ) → X ≃ Y)
corollary {𝓤} ua Y = equiv-to-singleton (equiv-classification ua Y) i
 where
  i : is-singleton (Y → 𝓢 𝓤)
  i = univalence-gives-vvfunext' (ua 𝓤) (ua (𝓤 ⁺))
        (λ y → the-singletons-form-a-singleton
                (univalence-gives-propext (ua 𝓤))
                (univalence-gives-dfunext (ua 𝓤)))
\end{code}

*Exercise*. (1) Show that the sections of `Y` are classified by the type `Σ \(A : 𝓤 ̇ ) → A` of pointed types.
(2) After we have defined [propositional truncations](HoTT-UF-Agda.html#truncation) and surjections, show that the surjections into `Y` are classified by the type `Σ \(A : 𝓤 ̇ ) → ∥ A ∥` of inhabited types.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="magmaequivalences"></a> Magma equivalences

We now define magma equivalences and show that the type of magma
equivalences is identified with the type of magma isomorphisms, assuming
univalence. For simplicity, we assume global univalence, from which we
get global function extensionality.

\begin{code}
module magma-equivalences (ua : Univalence) where

 dfe : global-dfunext
 dfe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua
\end{code}

The magma homomorphism and isomorphism conditions are subsingleton
types by virtue of the fact that the underlying type of a magma is a
set by definition.

\begin{code}
 being-magma-hom-is-a-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                   → is-subsingleton (is-magma-hom M N f)
 being-magma-hom-is-a-subsingleton M N f =
  Π-is-subsingleton dfe
    (λ x → Π-is-subsingleton dfe
             (λ y → magma-is-set N (f (x ·⟨ M ⟩ y)) (f x ·⟨ N ⟩ f y)))

 being-magma-iso-is-a-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                   → is-subsingleton (is-magma-iso M N f)
 being-magma-iso-is-a-subsingleton M N f (h , g , k , η , ε) (h' , g' , k' , η' , ε') = γ
  where
   p : h ≡ h'
   p = being-magma-hom-is-a-subsingleton M N f h h'
   q : g ≡ g'
   q = dfe (λ y → g y          ≡⟨ (ap g (ε' y))⁻¹ ⟩
                  g (f (g' y)) ≡⟨ η (g' y) ⟩
                  g' y         ∎)

   i : is-subsingleton (is-magma-hom N M g' × (g' ∘ f ∼ id) × (f ∘ g' ∼ id))
   i = ×-is-subsingleton
         (being-magma-hom-is-a-subsingleton N M g')
         (×-is-subsingleton
            (Π-is-subsingleton dfe (λ x → magma-is-set M (g' (f x)) x))
            (Π-is-subsingleton dfe (λ y → magma-is-set N (f (g' y)) y)))

   γ : (h , g , k , η , ε) ≡ (h' , g' , k' , η' , ε')
   γ = to-×-≡ p (to-Σ-≡ (q , i _ _))
\end{code}

By a magma equivalence we mean an equivalence which is a magma
homomorphism. This notion is again a subsingleton type.

\begin{code}
 is-magma-equiv : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-equiv M N f = is-equiv f × is-magma-hom M N f

 being-magma-equiv-is-a-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                     → is-subsingleton (is-magma-equiv M N f)
 being-magma-equiv-is-a-subsingleton M N f = ×-is-subsingleton
                                              (being-equiv-is-a-subsingleton dfe dfe f)
                                              (being-magma-hom-is-a-subsingleton M N f)
\end{code}

A function is a magma isomorphism if and only if it is a magma equivalence.

\begin{code}
 magma-isos-are-magma-equivs : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                             → is-magma-iso M N f
                             → is-magma-equiv M N f
 magma-isos-are-magma-equivs M N f (h , g , k , η , ε) = i , h
  where
   i : is-equiv f
   i = invertibles-are-equivs f (g , η , ε)

 magma-equivs-are-magma-isos : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                             → is-magma-equiv M N f
                             → is-magma-iso M N f
 magma-equivs-are-magma-isos M N f (i , h) = h , g , k , η , ε
  where
   g : ⟨ N ⟩ → ⟨ M ⟩
   g = inverse f i
   η : g ∘ f ∼ id
   η = inverse-is-retraction f i
   ε : f ∘ g ∼ id
   ε = inverse-is-section f i
   k : (a b : ⟨ N ⟩) → g (a ·⟨ N ⟩ b) ≡ g a ·⟨ M ⟩ g b
   k a b = g (a ·⟨ N ⟩ b)             ≡⟨ ap₂ (λ a b → g (a ·⟨ N ⟩ b)) ((ε a)⁻¹) ((ε b)⁻¹) ⟩
           g (f (g a) ·⟨ N ⟩ f (g b)) ≡⟨ ap g ((h (g a) (g b))⁻¹) ⟩
           g (f (g a ·⟨ M ⟩ g b))     ≡⟨ η (g a ·⟨ M ⟩ g b) ⟩
           g a ·⟨ M ⟩ g b             ∎
\end{code}

Because these two notions are subsingleton types, we conclude that
they are equivalent.

\begin{code}
 magma-iso-charac : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                  → is-magma-iso M N f ≃ is-magma-equiv M N f
 magma-iso-charac M N f = logically-equivalent-subsingletons-are-equivalent
                           (is-magma-iso M N f)
                           (is-magma-equiv M N f)
                           (being-magma-iso-is-a-subsingleton M N f)
                           (being-magma-equiv-is-a-subsingleton M N f)
                           (magma-isos-are-magma-equivs M N f ,
                            magma-equivs-are-magma-isos M N f)
\end{code}

And hence they are equal by univalence.

\begin{code}
 magma-iso-charac' : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                   → is-magma-iso M N f ≡ is-magma-equiv M N f
 magma-iso-charac' M N f = Eq-to-Id (ua (universe-of ⟨ M ⟩))
                            (is-magma-iso M N f)
                            (is-magma-equiv M N f)
                            (magma-iso-charac M N f)
\end{code}

And by function extensionality the *properties* of being a magma
isomorphism and a magma equivalence are the same:

\begin{code}
 magma-iso-charac'' : (M N : Magma 𝓤)
                    → is-magma-iso M N ≡ is-magma-equiv M N
 magma-iso-charac'' M N = dfe (magma-iso-charac' M N)
\end{code}

Hence the type of magma equivalences is equivalent, and therefore
equal, to the type of magma isomorphisms.

\begin{code}
 _≃ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
 M ≃ₘ N = Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-equiv M N f

 ≅ₘ-charac : (M N : Magma 𝓤)
           → (M ≅ₘ N) ≃ (M ≃ₘ N)
 ≅ₘ-charac M N = Σ-cong (magma-iso-charac M N)

 ≅ₘ-charac' : (M N : Magma 𝓤)
            → (M ≅ₘ N) ≡ (M ≃ₘ N)
 ≅ₘ-charac' M N = ap Σ (magma-iso-charac'' M N)
\end{code}

To conclude, we characterize magma identity as magma equivalence. For
this purpose, we first characterize transport of magma structure:

\begin{code}
 magma-structure : 𝓤 ̇ → 𝓤 ̇
 magma-structure X = is-set X × (X → X → X)

 structure-of : (M : Magma 𝓤) → magma-structure ⟨ M ⟩
 structure-of (X , s) = s

 transport-of-magma-structure : (X Y : 𝓤 ̇ )
                                (s : magma-structure X) (t : magma-structure Y)
                                (p : X ≡ Y)
                              → (transport magma-structure p s ≡ t)
                              ≃ is-magma-hom (X , s) (Y , t) (Id-to-fun p)
 transport-of-magma-structure X X (i , _·_) (j , _*_) (refl X) =
   ((i , _·_) ≡ (j , _*_))                       ≃⟨ a ⟩
   (_·_ ≡ _*_)                                   ≃⟨ b ⟩
   ((x : X) → (λ x' → x · x') ≡ (λ x' → x * x')) ≃⟨ c ⟩
   ((x x' : X) → x · x' ≡ x * x')                ■
  where
   a = ≃-sym (embedding-criterion-converse pr₂
               (pr₂-embedding (is-set X) (X → X → X) (being-set-is-a-subsingleton dfe))
               (i , _·_)
               (j , _*_))
   b = happly _·_ _*_ , hfe _·_ _*_
   c = Π-cong dfe dfe X _ _ (λ x → happly (x ·_) (x *_) , hfe (x ·_) (x *_))
\end{code}

Magma identity is equivalent to magma equivalence, and hence to magma isomorphism:

\begin{code}
 magma-identity-is-equivalence : (M N : Magma 𝓤) → (M ≡ N) ≃ (M ≃ₘ N)
 magma-identity-is-equivalence {𝓤} M N =
   (M ≡ N)                                                                                   ≃⟨ a ⟩
   (Σ \(p : ⟨ M ⟩ ≡ ⟨ N ⟩) → transport magma-structure p (structure-of M) ≡ structure-of N)  ≃⟨ b ⟩
   (Σ \(p : ⟨ M ⟩ ≡ ⟨ N ⟩) → is-magma-hom M N (Eq-to-fun (Id-to-Eq ⟨ M ⟩ ⟨ N ⟩ p)))          ≃⟨ c ⟩
   (Σ \(e : ⟨ M ⟩ ≃ ⟨ N ⟩) → is-magma-hom M N (Eq-to-fun e))                                 ≃⟨ Σ-assoc ⟩
   (Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-equiv f × is-magma-hom M N f)                                ■
  where
   a = Σ-≡-≃ M N
   b = Σ-cong (transport-of-magma-structure ⟨ M ⟩ ⟨ N ⟩ (structure-of M) (structure-of N))
   c = ≃-sym (Σ-change-of-variables-hae
                (λ e → is-magma-hom M N (Eq-to-fun e))
                (Id-to-Eq ⟨ M ⟩ ⟨ N ⟩)
                (Id-to-Eq-is-hae (ua 𝓤) (ua (𝓤 ⁺))))

 magma-identity-is-isomorphism : (M N : Magma 𝓤) → (M ≡ N) ≃ (M ≅ₘ N)
 magma-identity-is-isomorphism M N =
   (M ≡ N)  ≃⟨ magma-identity-is-equivalence M N ⟩
   (M ≃ₘ N) ≃⟨ ≃-sym (≅ₘ-charac M N) ⟩
   (M ≅ₘ N) ■
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="sip"></a> Structure identity principle

For the moment, see [this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-StructureIdentityPrinciple.html).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="truncation"></a> Subsingleton truncation

The following is Voevosky's approach to saying that a type is
inhabited in such a way that the statement of inhabitation is a
subsingleton, using `funext`.

\begin{code}
is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P
\end{code}

This says that if we have a function from `X` to a subsingleton `P`, then
`P` must have a point. So this fails when `X=𝟘`. Considering `P=𝟘`, we conclude
that `¬¬ X` if `X` is inhabited, which says that `X` is non-empty. However,
in the absence of excluded middle, [inhabitation is stronger than
non-emptiness](https://lmcs.episciences.org/3217).

For simplicity in the formulation of the theorems, we assume global
function extensionality.
A type can be pointed in many ways, but inhabited in at most one way:

\begin{code}
inhabitation-is-a-subsingleton : global-dfunext → (X : 𝓤 ̇ )
                               → is-subsingleton (is-inhabited X)
inhabitation-is-a-subsingleton fe X =
 Π-is-subsingleton fe
   λ P → Π-is-subsingleton fe
          (λ (s : is-subsingleton P)
                → Π-is-subsingleton fe (λ (f : X → P) → s))

pointed-is-inhabited : {X : 𝓤 ̇ } → X → is-inhabited X
pointed-is-inhabited x = λ P s f → f x

inhabited-recursion : (X P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion X P s f φ = φ P s f
\end{code}

We can derive induction from recursion in this case, but the
"computation rule" holds up to an identification, rather than
judgmentally:

\begin{code}
inhabited-induction : global-dfunext
                    → {X : 𝓤 ̇ } {P : is-inhabited X → 𝓤 ̇ }
                    → (i : (s : is-inhabited X) → is-subsingleton (P s))
                    → (f : (x : X) → P (pointed-is-inhabited x))
                    → (s : is-inhabited X) → P s
inhabited-induction fe {X} {P} i f s = φ' s
 where
  φ : X → P s
  φ x = transport P (inhabitation-is-a-subsingleton fe X (pointed-is-inhabited x) s) (f x)
  φ' : is-inhabited X → P s
  φ' = inhabited-recursion X (P s) (i s) φ

inhabited-computation : (fe : global-dfunext) {X : 𝓤 ̇ } {P : is-inhabited X → 𝓤 ̇ }
                      → (i : (s : is-inhabited X) → is-subsingleton (P s))
                      → (f : (x : X) → P (pointed-is-inhabited x))
                      → (x : X)
                      → inhabited-induction fe i f (pointed-is-inhabited x) ≡ f x
inhabited-computation fe i f x = i (pointed-is-inhabited x)
                                   (inhabited-induction fe i f (pointed-is-inhabited x))
                                   (f x)
\end{code}

Although we [don't necessarily have](HoTT-UF-Agda.html#moreexercises) that
`¬¬ P → P`, we do have that `is-inhabited P → P` if `P` is a subsingleton:

\begin{code}
inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ )
                                          → is-subsingleton P → is-inhabited P → P
inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s (𝑖𝑑 P)

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
image' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image' f = Σ \(y : codomain f) → is-inhabited (Σ \(x : domain f) → f x ≡ y)
\end{code}

An attempt to define the image of `f` without the inhabitation
predicate would be to take it to be

   > `Σ \(y : codomain f) → Σ \(x : domain f) → f x ≡ y`.

But we [already know](HoTT-UF-Agda.html#total-fiber-is-domain) that
this is equivalent to `X`.  This is similar to what happens in set
theory: the graph of any function is in bijection with its domain.


We can define the restriction and corestriction of a function to its
image as follows:

\begin{code}
restriction' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → image' f → Y
restriction' f (y , _) = y

corestriction' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → X → image' f
corestriction' f x = f x , pointed-is-inhabited (x , refl (f x))
\end{code}

And we can define the notion of surjection as follows:
\begin{code}
is-surjection' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection' f = (y : codomain f) → is-inhabited (Σ \(x : domain f) → f x ≡ y)
\end{code}

*Exercise.* The type `(y : codomain f) → Σ \(x : domain f) → f x ≡ y`
 is equivalent to the type `has-section f`, which is stronger than
 saying that `f` is a surjection.

\begin{code}
has-section-charac : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → ((y : Y) → Σ \(x : X) → f x ≡ y) ≃ has-section f
\end{code}

There are two problems with this definition of inhabitation:

  * Inhabitation has values in the next universe.

  * We can eliminate into subsingletons of the same universe only.

In particular, it is not possible to show that the map `X →
is-inhabited X` is a surjection, or that `X → Y` gives `is-inhabited X
→ is-inhabited Y` for `X` and `Y` in arbitrary universes.

There are two proposed ways to solve this kind of problem:

  * Voevodsky works with certain [resizing
    rules](http://www.math.ias.edu/vladimir/files/2011_Bergen.pdf) for
    subsingletons. At the time of writing, the (relative) consistency
    of the system with such rules is an open question.

  * The HoTT book works with certain higher inductive types (HIT's),
    which are known to have models and hence to be (relatively)
    consistent.  This is the same approach adopted by cubical type
    theory and cubical Agda.

A third possibility is to work with subsingleton truncations
[axiomatically](https://lmcs.episciences.org/3217), which is compatible
with the above two proposals. We write this axiom as a record type
rather than as an iterated `Σ` type for simplicity, where we use the
HoTT-book notation `∥ X ∥` for the inhabitation of `X`,
called the propositional, or subsingleton, truncation of `X`:

\begin{code}
record subsingleton-truncations-exist : 𝓤ω where
 field
  ∥_∥                  : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-a-subsingleton : {𝓤 : Universe} {X : 𝓤 ̇ } → is-subsingleton ∥ X ∥
  ∣_∣                 : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-recursion         : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                       → is-subsingleton P → (X → P) → ∥ X ∥ → P
\end{code}

This is the approach we adopt in our [personal Agda
development](http://www.cs.bham.ac.uk/~mhe/agda-new/).

We now assume that subsingleton truncations exist in the next few
constructions, and we `open` the assumption to make the above fields
visible.

\begin{code}
module basic-truncation-development
         (pt : subsingleton-truncations-exist)
         (fe : global-dfunext)
       where

  open subsingleton-truncations-exist pt public

  ∥∥-induction : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
              → ((s : ∥ X ∥) → is-subsingleton (P s))
              → ((x : X) → P ∣ x ∣)
              → (s : ∥ X ∥) → P s
  ∥∥-induction {𝓤} {𝓥} {X} {P} i f s = φ' s
   where
    φ : X → P s
    φ x = transport P (∥∥-is-a-subsingleton ∣ x ∣ s) (f x)
    φ' : ∥ X ∥ → P s
    φ' = ∥∥-recursion (i s) φ

  ∥∥-computation : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
                → (i : (s : ∥ X ∥) → is-subsingleton (P s))
                → (f : (x : X) → P ∣ x ∣)
                → (x : X)
                → ∥∥-induction i f ∣ x ∣ ≡ f x
  ∥∥-computation i f x = i ∣ x ∣ (∥∥-induction i f ∣ x ∣) (f x)

  ∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
  ∥∥-functor f = ∥∥-recursion ∥∥-is-a-subsingleton (λ x → ∣ f x ∣)

  ∃ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃ A = ∥ Σ A ∥

  ∃! : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃! A = is-singleton (Σ A)

  _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ∨ B = ∥ A + B ∥
\end{code}

The subsingleton truncation of a type and its inhabitation are
logically equivalent propositions:

\begin{code}
  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇ ) → ∥ X ∥ ⇔ is-inhabited X
  ∥∥-agrees-with-inhabitation X = a , b
   where
    a : ∥ X ∥ → is-inhabited X
    a = ∥∥-recursion (inhabitation-is-a-subsingleton fe X) pointed-is-inhabited
    b : is-inhabited X → ∥ X ∥
    b = inhabited-recursion X ∥ X ∥ ∥∥-is-a-subsingleton ∣_∣
\end{code}

Hence they differ only in size, and when size matters don't get on the
way, we can use `is-inhabited` instead of `∥_∥` if we wish.

\begin{code}
  image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
  image f = Σ \(y : codomain f) → ∃ \(x : domain f) → f x ≡ y

  restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → image f → Y
  restriction f (y , _) = y

  corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → X → image f
  corestriction f x = f x , ∣ (x , refl (f x)) ∣

  is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
  is-surjection f = (y : codomain f) → ∃ \(x : domain f) → f x ≡ y
\end{code}

This time we can prove that the map `x ↦ ∣ x ∣` of `X` into `∥ X ∥` is a surjection without the universe levels getting in our way:

\begin{code}
  ∣∣-is-surjection : (X : 𝓤 ̇ ) → is-surjection (λ (x : X) → ∣ x ∣)
  ∣∣-is-surjection X s = γ
   where
    f : X → ∃ \(x : X) → ∣ x ∣ ≡ s
    f x = ∣ (x , ∥∥-is-a-subsingleton ∣ x ∣ s) ∣
    γ : ∃ \(x : X) → ∣ x ∣ ≡ s
    γ = ∥∥-recursion ∥∥-is-a-subsingleton f s
\end{code}

Saying that this surjection `X → ∥ X ∥` has a section for all `X` (we
can pick a point of every inhabited type) amounts to [global
choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice), which
[contradicts univalence](https://homotopytypetheory.org/book/), and
also [gives classical logic](https://lmcs.episciences.org/3217).

*Exercise*. If `X` and `Y` are types obtained by summing `x-` and
  `y`-many copies of the type `𝟙`, respectively, as in `𝟙 + 𝟙 + ... + 𝟙` , where `x`
  and `y` are natural numbers, then `∥ X ≡ Y ∥ ≃ (x ≡ y)` and the type
  `X ≡ X` has `x!` elements.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="choice"></a> The univalent axiom of choice

The axiom of choice says that if for every `x : X` there exists `a : A
x` with `R x a`, where `R` is some given relation, then there exists a
choice function `f : (x : X) → A x` with `R x (f x)` for all `x :
X`. This is not provable or disprovable in univalent mathematics, but
it does hold in [Voevodsky's simplicial
model](https://arxiv.org/abs/1211.2851) of our univalent type theory,
and hence is consistent, provided:

 * `X` is a set,
 * `A` is a family of sets,
 * the relation `R` is subsingleton valued.

\begin{code}
  AC : ∀ 𝓣 (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X → ((x : X) → is-set (A x)) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
  AC 𝓣 X A i j = (R : (x : X) → A x → 𝓣 ̇ )
               → ((x : X) (a : A x) → is-subsingleton (R x a))

               → ((x : X) → ∃ \(a : A x) → R x a)
               → ∃ \(f : (x : X) → A x) → (x : X) → R x (f x)
\end{code}

We define the axiom of choice in the universe `𝓤` to be the above with
`𝓣 = 𝓤`, for all possible `X` and `A` (and `R`).

\begin{code}
  Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
  Choice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ )
             (i : is-set X) (j : (x : X) → is-set (A x))
           → AC 𝓤 X A i j
\end{code}

It is important that we have the condition that `A` is a set-indexed
family of sets and that the relation `R` is subsingleton valued. For
arbitrary higher groupoids, it is not in general possible to perform
the choice functorially.

The above is equivalent to another familiar formulation of choice,
namely that a set-indexed product of non-empty sets is non-empty,
where in a constructive setting we strengthen `non-empty` to
`inhabited` (but this strengthening is immaterial, because choice
implies excluded middle, and excluded middle implies that
non-emptiness and inhabitation are the same notion).

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
    k : (x : X) (y : Y x) → is-subsingleton (R x y)
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

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="appendix"></a> Appendix

### <a id="infixop"></a> Operator fixities and precedences


Without the following list of operator precedences and
associativities (left or right), this agda file doesn't parse and is
rejected by Agda.


\begin{code}

infix  4  _∼_
infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_
infix  0 _≡_
infixl 2 _∙_
infixr 0 _≡⟨_⟩_
infix  1 _∎
infix  3  _⁻¹
infix  0 _◁_
infix  1 _◀
infixr 0 _◁⟨_⟩_
infix  0 _≃_
infixl 2 _●_
infixr 0 _≃⟨_⟩_
infix  1 _■

\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="moreexercises"></a> Additional exercises

Solutions are available [at the end](#mlttexercisessol).

*Exercise.* A sequence of elements of a type `X` is just a function `ℕ
 → X`. Use [Cantor's diagonal
 argument](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)
 to show in Agda that the type of sequences of natural numbers is
 uncountable. Prove a positive version and then derive a negative
 version from it:

\begin{code}
positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)
\end{code}

*Hint.* It may be helpful to prove that the function `succ` has no fixed points, first.

\begin{code}
𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
\end{code}

Now we would like to have `(𝟚 ≡ 𝟚) ≡ 𝟚` with univalence, but the
problem is that the type `𝟚 ≡ 𝟚` lives in `𝓤₁` whereas `𝟚` lives in
`𝓤₀` and so, having different types, can't be compared for equality.
But we do have that

\begin{code}
lifttwo : is-univalent 𝓤₀
        → is-univalent 𝓤₁
        → (𝟚 ≡ 𝟚) ≡ Lift 𝓤₁ 𝟚
\end{code}

We now discuss alternative formulations of the principle of excluded middle.

\begin{code}
DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → ¬¬ P → P

neg-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ ) → is-subsingleton (¬ X)

emsanity : dfunext 𝓤 𝓤₀ → (P : 𝓤 ̇ ) → is-subsingleton P → is-subsingleton (P + ¬ P)

ne : (X : 𝓤 ̇ ) → ¬¬(X + ¬ X)

DNE-gives-EM : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤

EM-gives-DNE : EM 𝓤 → DNE 𝓤
\end{code}

The following says that excluded middle holds if and only if every
subsingleton is the negation of some type.

\begin{code}
SN : ∀ 𝓤 → 𝓤 ⁺ ̇
SN 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → Σ \(X : 𝓤 ̇ ) → P ⇔ ¬ X

SN-gives-DNE : SN 𝓤 → DNE 𝓤

DNE-gives-SN : DNE 𝓤 → SN 𝓤
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)

### <a id="mlttexercisessol"></a> Solutions

In our first solution, we apply propositional extensionality to
show that `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`.

\begin{code}
module ℕ-more where

  open ℕ-order
  open Arithmetic renaming (_+_ to _∔_)
  open BasicArithmetic
\end{code}

[Recall](HoTT-UF-Agda.html#basicarithmetic) that we defined `x ≼ y` to
mean `Σ \(z : ℕ) → x + z ≡ y`.  First we show that both relations are
proposition valued:

\begin{code}
  ≤-prop-valued : (x y : ℕ) → is-prop (x ≤ y)
  ≤-prop-valued 0 y               = 𝟙-is-subsingleton
  ≤-prop-valued (succ x) zero     = 𝟘-is-subsingleton
  ≤-prop-valued (succ x) (succ y) = ≤-prop-valued x y

  ≼-prop-valued : (x y : ℕ) → is-prop (x ≼ y)
  ≼-prop-valued x y (z , p) (z' , p') = to-Σ-≡ (q , r)
   where
    q : z ≡ z'
    q = +-lc x z z' (x ∔ z  ≡⟨ p ⟩
                     y      ≡⟨ p' ⁻¹ ⟩
                     x ∔ z' ∎)
    r : transport (λ - → x ∔ - ≡ y) q p ≡ p'
    r = ℕ-is-set (x ∔ z') y (transport (λ - → x ∔ - ≡ y) q p) p'

  ≤-charac : propext 𝓤₀ → (x y : ℕ) → (x ≤ y) ≡ (x ≼ y)
  ≤-charac pe x y = pe (≤-prop-valued x y) (≼-prop-valued x y)
                       (≤-gives-≼ x y) (≼-gives-≤ x y)
\end{code}

This completes the exercise on the order relation on the natural numbers.

For the moment we leave the following solutions unexplained.

\begin{code}
has-section-charac f = ΠΣ-distr-≃

succ-no-fixed-point : (n : ℕ) → succ n ≢ n
succ-no-fixed-point 0        = positive-not-zero 0
succ-no-fixed-point (succ n) = γ
 where
  IH : succ n ≢ n
  IH = succ-no-fixed-point n
  γ : succ (succ n) ≢ succ n
  γ p = IH (succ-lc p)

positive-cantors-diagonal e = (α , φ)
 where
  α : ℕ → ℕ
  α n = succ(e n n)
  φ : (n : ℕ) → α ≢ e n
  φ n p = succ-no-fixed-point (e n n) q
   where
    q = succ (e n n)  ≡⟨ refl (α n) ⟩
        α n           ≡⟨ ap (λ - → - n) p ⟩
        e n n         ∎

cantors-diagonal (e , γ) = c
 where
  α :  ℕ → ℕ
  α = pr₁ (positive-cantors-diagonal e)
  φ : (n : ℕ) → α ≢ e n
  φ = pr₂ (positive-cantors-diagonal e)
  b : Σ \(n : ℕ) → α ≡ e n
  b = γ α
  c : 𝟘
  c = φ (pr₁ b) (pr₂ b)

𝟚-has-𝟚-automorphisms fe = invertibility-gives-≃ f (g , η , ε)
 where
  f : (𝟚 ≃ 𝟚) → 𝟚
  f (h , e) = h ₀
  g : 𝟚 → (𝟚 ≃ 𝟚)
  g ₀ = id , id-is-equiv 𝟚
  g ₁ = swap₂ , swap₂-is-equiv
  η : (e : 𝟚 ≃ 𝟚) → g (f e) ≡ e
  η (h , e) = γ (h ₀) (h ₁) (refl (h ₀)) (refl (h ₁))
   where
    γ : (m n : 𝟚) → h ₀ ≡ m → h ₁ ≡ n → g (h ₀) ≡ (h , e)
    γ ₀ ₀ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₀   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))
    γ ₀ ₁ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₀) ₀     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₀) ₁     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)),
                       being-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₀ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₁) ₀     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₁) ₁     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)),
                       being-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₁ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₁   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))

  ε : (n : 𝟚) → f (g n) ≡ n
  ε ₀ = refl ₀
  ε ₁ = refl ₁


lifttwo ua₀ ua₁ = Eq-to-Id ua₁ (𝟚 ≡ 𝟚) (Lift 𝓤₁ 𝟚) e
 where
  e = (𝟚 ≡ 𝟚)   ≃⟨ Id-to-Eq 𝟚 𝟚 , ua₀ 𝟚 𝟚 ⟩
      (𝟚 ≃ 𝟚)   ≃⟨ 𝟚-has-𝟚-automorphisms (univalence-gives-dfunext ua₀) ⟩
      𝟚         ≃⟨ ≃-sym (Lift-≃ 𝟚) ⟩
      Lift 𝓤₁ 𝟚 ■

neg-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))

emsanity fe P i (inl p) (inl q) = ap inl (i p q)
emsanity fe P i (inl p) (inr n) = !𝟘 (inl p ≡ inr n) (n p)
emsanity fe P i (inr m) (inl q) = !𝟘 (inr m ≡ inl q) (m q)
emsanity fe P i (inr m) (inr n) = ap inr (neg-is-subsingleton fe P m n)

ne X = λ (f : ¬(X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM fe dne P i = dne (P + ¬ P) (emsanity fe P i) (ne P)

EM-gives-DNE em P i = γ (em P i)
 where
  γ : P + ¬ P → ¬¬ P → P
  γ (inl p) φ = p
  γ (inr n) φ = !𝟘 P (φ n)

SN-gives-DNE {𝓤} sn P i = h
 where
  X : 𝓤 ̇
  X = pr₁ (sn P i)
  f : P → ¬ X
  f = pr₁ (pr₂ (sn P i))
  g : ¬ X → P
  g = pr₂ (pr₂ (sn P i))
  f' : ¬¬ P → ¬(¬¬ X)
  f' = contrapositive (contrapositive f)
  h : ¬¬ P → P
  h = g ∘ tno X ∘ f'
  h' : ¬¬ P → P
  h' φ = g (λ (x : X) → φ (λ (p : P) → f p x))

DNE-gives-SN dne P i = (¬ P) , dni P , dne P i
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
