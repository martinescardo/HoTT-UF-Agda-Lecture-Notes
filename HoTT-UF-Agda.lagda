---
layout: default
title : Introduction to Homotopy Type Theory and Univalent Foundations (HoTT/UF) with Agda
date : 2019-03-04
---
<!--

  * The file HoTT-UF-Agda.lagda is *not* meant to be read by people.

  * It is used to automatically generate the following files, which are
    meant to be read by people:

    - https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html

    - https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.pdf

    - https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/tree/master/agda

  * The html file is better rendered and probably easier to read than
    the pdf file, but both have internal links, including to the Agda
    definitions.

  * Warning: this file takes a long time to be checked by Agda.  We
    are avoiding a modular development so that a single pdf file with
    internal links, including to the Agda definitions, can be
    produced. This works by first using Agda to generate html for the
    Agda code, then using jekyll to process the markdown code to
    generate html for everything else, and finally using google-chrome
    in headless mode to generate pdf from the html code.  See the makefile.

-->
## <a id="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

4th March 2019, version of {{ "now" | date: "%d %B %Y, %H:%M" }}.

[Martín Hötzel Escardó](https://www.cs.bham.ac.uk/~mhe/),
[School of Computer Science](https://www.cs.bham.ac.uk/),
[University of Birmingham](http://www.bham.ac.uk/),
UK.

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)

**Abstract.** We introduce [Voevodsky](https://www.math.ias.edu/Voevodsky/)'s [univalent foundations](https://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01616-9/) and
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

We also [fully discuss and emphasize](HoTT-UF-Agda.html#summary) that
classical axioms can be assumed consistently in univalent mathematics.

**Keywords.** Univalent mathematics. Univalent foundations. Univalent
  type theory. Univalence axiom. `∞`-Groupoid. Homotopy type. Type
  theory. Homotopy type theory. Intensional Martin-Löf type
  theory. Dependent type theory. Identity type. Type
  universe. Constructive mathematics. Agda. Cubical type
  theory. Cubical Agda. Computer-verified mathematics.

**About this document.**
[This](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes) is
a set of so-called
[literate](https://agda.readthedocs.io/en/latest/tools/literate-programming.html)
Agda files, with the formal, verified, mathematical development within
*code* environments, and the usual mathematical discussion outside
them.  Most of this file is not Agda code, and is in markdown format,
and the html web page is generated automatically from it using Agda
and other
tools. [Github](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes)
issues or pull requests by students to fix typos or mistakes and
clarify ambiguities are welcome.  There is also a [pdf
version](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.pdf)
with internal links to sections and Agda definitions, which is
automatically generated from the [html
version](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html).
These notes were originally developed for the [Midlands Graduate
School 2019](http://events.cs.bham.ac.uk/mgs2019/). They will evolve
for a while.

<!--
The version at *ResearchGate* is usually out of date. Instead see [this](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html), from which an up to date pdf file may be downloaded.
-->

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)
### <a id="introduction"></a> Introduction

A univalent type theory is the underlying formal system for a
foundation of univalent mathematics as conceived by [Voevodsky](https://www.math.ias.edu/Voevodsky/).

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
to account for the size distinction.

In particular, properties of monoids are automatically invariant under
isomorphism, properties of categories are automatically invariant
under equivalence, and so son.

Voevodsky's way to achieve this is to start with a Martin-Löf type
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
by the univalence axiom alone. In fact, half of these notes begin
*without* the univalence axiom.

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
surjective function).

We will not assume univalence and truncation globally, so that the
students can see clearly when they are or are not needed. In fact, the
foundational definitions, constructions, theorems and proofs of
univalent mathematics don't require univalence or propositional
truncation, and so can be developed in a version of the original
Martin-Löf type theories, and this is what happens in these notes, and
what Voevodsky did in his brilliant [original development in the
computer system Coq](https://github.com/UniMath/Foundations). Our use
of Agda, rather than Coq, is a personal matter of taste only, and the
students are encouraged to learn Coq, too.

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

In particular, it is recommended to read the concluding notes for each
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
   - [Cubical Agda blog post](https://homotopytypetheory.org/2018/12/06/cubical-agda/) by Anders Mörtberg.
   - [Cubical Agda documentation](https://agda.readthedocs.io/en/latest/language/cubical.html#cubical).

Regarding the genesis of the subject:

   - [A very short note on homotopy λ-calculus](http://math.ucr.edu/home/baez/Voevodsky_note.ps).
   - [Notes on homotopy λ-calculus](https://github.com/vladimirias/2006_03_Homotopy_lambda_calculus/blob/master/homotopy_lambda_calculus_Mar_5_2006.pdf).

Voevodsky [says](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2014_04_22_slides.pdf)
that he was influenced by [Makkai](https://www.math.mcgill.ca/makkai/)'s thinking:

   - [FOLDS](https://www.math.mcgill.ca/makkai/folds/foldsinpdf/FOLDS.pdf).
   - [The theory of abstract sets based on first-order logic with dependent types](https://www.math.mcgill.ca/makkai/Various/MateFest2013.pdf).

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

We also have an [Agda development](https://www.cs.bham.ac.uk/~mhe/agda-new/)
of [univalent
foundations](https://www.cs.bham.ac.uk/~mhe/agda-new/UF.html) which is
applied to work on [injective
types](https://www.cs.bham.ac.uk/~mhe/agda-new/InjectiveTypes-article.html),
[compact (or searchable)
types](https://www.cs.bham.ac.uk/~mhe/agda-new/Compactness.html),
[compact
ordinals](https://www.cs.bham.ac.uk/~mhe/agda-new/Ordinals.html) and
[more](https://www.cs.bham.ac.uk/~mhe/agda-new/SafeModulesIndex.html).

[<sub>Table of contents ⇓</sub>](HoTT-UF-Agda.html#contents)
### <a id="plan"></a> Choice of material

This is intended as an introductory graduate course. We include what
we regard as the essence of univalent foundations and univalent
mathematics, but we are certainly omitting important material that is
needed to do univalent mathematics in practice, and the readers who wish
to practice univalent mathematics should consult the above references.

### <a id="contents"></a> Table of contents

  1. [Front matter](HoTT-UF-Agda.html#lecturenotes)
     1. [Title, abstract, keywords and about](HoTT-UF-Agda.html#lecturenotes)
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
     1. [Singletons, subsingletons and sets](HoTT-UF-Agda.html#subsingletonsandsets)
        1. [Singleton (or contractible) types](HoTT-UF-Agda.html#singleton-types)
        1. [Subsingletons (or propositions or truth values)](HoTT-UF-Agda.html#subsingleton-types)
        1. [Sets](HoTT-UF-Agda.html#set-types)
     1. [Univalent excluded middle](HoTT-UF-Agda.html#em)
     1. [The types of magmas and monoids](HoTT-UF-Agda.html#magmasandmonoids)
     1. [The identity type in univalent mathematics](HoTT-UF-Agda.html#identitytypeuf)
     1. [Identifications that depend on identifications](HoTT-UF-Agda.html#dependentequality)
     1. [Equality in Σ types](HoTT-UF-Agda.html#sigmaequality)
     1. [Voevodsky's notion of hlevel](HoTT-UF-Agda.html#hlevel)
        1. [Hedberg's Theorem](HoTT-UF-Agda.html#hedberg)
        1. [A characterization of sets](HoTT-UF-Agda.html#setscharacterization)
        1. [Subsingletons are sets](HoTT-UF-Agda.html#subsingletonsaresets)
        1. [The types of hlevel 1 are the subsingletons](HoTT-UF-Agda.html#hlevel1subsingleton)
        1. [The types of hlevel 2 are the sets](HoTT-UF-Agda.html#hlevel2set)
        1. [The hlevels are upper closed](HoTT-UF-Agda.html#hlevelsupper)
        1. [`ℕ` and `𝟚` are sets](HoTT-UF-Agda.html#naturalsset)
     1. [Retracts](HoTT-UF-Agda.html#retracts)
     1. [Voevodsky's notion of type equivalence](HoTT-UF-Agda.html#fibersandequivalences)
     1. [Voevodsky's univalence axiom](HoTT-UF-Agda.html#univalence)
     1. [Example of a type that is not a set under univalence](HoTT-UF-Agda.html#notsets)
     1. [Exercises](HoTT-UF-Agda.html#lefttothereader)
        1. [Formulations](HoTT-UF-Agda.html#formulations)
        1. [Solutions](HoTT-UF-Agda.html#solutions)
     1. [A characterization of univalence](HoTT-UF-Agda.html#unicharac)
     1. [Equivalence induction](HoTT-UF-Agda.html#equivalenceinduction)
     1. [Half adjoint equivalences](HoTT-UF-Agda.html#haes)
     1. [Function extensionality from univalence](HoTT-UF-Agda.html#funextfromua)
     1. [Variations of function extensionality and their logical equivalence](HoTT-UF-Agda.html#hfunext)
     1. [Universes are map classifiers](HoTT-UF-Agda.html#typeclassifier)
     1. [The univalence axiom is a (sub)singleton type](HoTT-UF-Agda.html#univalencesubsingleton)
     1. [Unique existence in univalent mathematics](HoTT-UF-Agda.html#unique-existence)
     1. [Universal property of the natural numbers](HoTT-UF-Agda.html#nnt)
     1. [More consequences of function extensionality](HoTT-UF-Agda.html#morefunextuses)
     1. [Propositional extensionality and the powerset](HoTT-UF-Agda.html#propositionalextensionality)
     1. [Some constructions with types of equivalences](HoTT-UF-Agda.html#equivconstructions)
     1. [Type embeddings](HoTT-UF-Agda.html#embeddings)
     1. [The Yoneda Lemma for types](HoTT-UF-Agda.html#yoneda)
     1. [Universe lifting](HoTT-UF-Agda.html#universelifting)
     1. [The subtype classifier and other classifiers](HoTT-UF-Agda.html#subtypeclassifier)
     1. [Magma equivalences](HoTT-UF-Agda.html#magmaequivalences)
     1. [Equality of mathematical structures](HoTT-UF-Agda.html#sip)
        1. [A structure identity principle for a standard notion of structure](HoTT-UF-Agda.html#sns)
        1. [∞-Magmas](HoTT-UF-Agda.html#infty-magmas)
        1. [Adding axioms](HoTT-UF-Agda.html#adding-axioms)
        1. [Magmas](HoTT-UF-Agda.html#magmas-sip)
        1. [Pointed types](HoTT-UF-Agda.html#pointed-types)
        1. [Combining two mathematical structures](HoTT-UF-Agda.html#combining-structures)
        1. [Pointed ∞-magmas](HoTT-UF-Agda.html#pointed-infty-magmas)
        1. [Monoids](HoTT-UF-Agda.html#monoids-sip)
        1. [Groups](HoTT-UF-Agda.html#groups-sip)
        1. [The slice type](HoTT-UF-Agda.html#slice-sip)
        1. [Metric spaces, graphs and ordered structures](HoTT-UF-Agda.html#metric-sip)
        1. [Topological spaces](HoTT-UF-Agda.html#topological-sip)
        1. [Selection spaces](HoTT-UF-Agda.html#selection-sip)
        1. [A contrived example](HoTT-UF-Agda.html#contrived-sip)
        1. [Functor algebras](HoTT-UF-Agda.html#functor-algebras-sip)
        1. [Type-valued preorders](HoTT-UF-Agda.html#infty-preorders-sip)
        1. [Categories](HoTT-UF-Agda.html#categories-sip)
     1. [Subsingleton truncation](HoTT-UF-Agda.html#truncation)
        1. [Voevodsky's approach to subsingleton truncation](HoTT-UF-Agda.html#vvaproach)
        1. [An axiomatic approach](HoTT-UF-Agda.html#axiomatic-approach)
        1. [Disjunction and existence](HoTT-UF-Agda.html#disjunction-and-existence)
        1. [Images and surjections](HoTT-UF-Agda.html#images-and-surjections)
        1. [A characterization of equivalences](HoTT-UF-Agda.html#equivalence-characterization)
        1. [Exiting truncations](HoTT-UF-Agda.html#exiting-truncations)
     1. [Choice in univalent mathematics](HoTT-UF-Agda.html#choice)
        1. [Unique choice](HoTT-UF-Agda.html#unique-choice)
        1. [Univalent choice](HoTT-UF-Agda.html#univalent-choice)
        1. [A second formulation of univalent choice](HoTT-UF-Agda.html#univalent-choice2)
        1. [A third formulation of univalent choice](HoTT-UF-Agda.html#univalent-choice3)
        1. [Univalent choice gives excluded middle](HoTT-UF-Agda.html#choice-gives-excluded middle)
        1. [Global choice](HoTT-UF-Agda.html#global-choice)
     1. [Propositional resizing, truncation and the powerset](HoTT-UF-Agda.html#resizing)
        1. [Propositional resizing](HoTT-UF-Agda.html#prop-resizing)
        1. [Excluded middle gives propositional resizing](HoTT-UF-Agda.html#em-resizing)
        1. [The propositional resizing axiom is a subsingleton](HoTT-UF-Agda.html#resizing-subsingleton)
        1. [Propositional impredicativity](HoTT-UF-Agda.html#prop-impred)
        1. [Propositional resizing gives subsingleton truncation](HoTT-UF-Agda.html#truncation-from-resizing)
        1. [The powerset in the presence of propositional resizing](HoTT-UF-Agda.html#powerset-resizing)
        1. [Topological spaces in the presence of propositional resizing](HoTT-UF-Agda.html#topol-resizing)
     1. [Quotients](HoTT-UF-Agda.html#quotients)
     1. [Summary of consistent axioms for univalent mathematics](HoTT-UF-Agda.html#summary)
  1. [Appendix](HoTT-UF-Agda.html#appendix)
     1. [Solutions to some exercises](HoTT-UF-Agda.html#someexercisessol)
     1. [Additional exercises](HoTT-UF-Agda.html#moreexercises)
     1. [Solutions to additional exercises](HoTT-UF-Agda.html#additionalexercisessol)
     1. [Operator fixities and precedences](HoTT-UF-Agda.html#infixop)
     1. [Agda files automatically extracted from these notes](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/tree/master/agda)
     1. [The sources for these notes](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes)
     1. [License](https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes/blob/master/LICENSE)

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

 * The option [`--without-K`](https://agda.readthedocs.io/en/latest/language/without-k.html) disables [Streicher's `K` axiom](https://ncatlab.org/nlab/show/axiom+K+%28type+theory%29), which we [don't
   want](HoTT-UF-Agda.html#identitytype) for univalent mathematics.

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

The Agda code in these notes has syntax highlighting and links (in the
[html](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html)
and
[pdf](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.pdf)
versions), so that we can navigate to the definition of a name or
symbol by clicking at it.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="universes"></a> Universes

A universe `𝓤` is a type of types.

 1. One use of universes is to define families of types indexed by a
    type `X` as functions `X → 𝓤`.

 1. Such a function is [sometimes](HoTT-UF-Agda.html#twinprime) seen
    as a property of elements of `X`.

 1. Another use of universes, as we shall see, is to define types of
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
`𝓤₁`. According to the above discussion, we have

   > `𝓤 ̇ : 𝓤 ⁺ ̇`

The least upper bound of two universes `𝓤` and `𝓥` is written

   > `𝓤 ⊔ 𝓥`.

For example, if `𝓤` is `𝓤₀` and `𝓥` is `𝓤₁`, then `𝓤 ⊔ 𝓥` is `𝓤₁`.

We now bring our notation for universes by importing our Agda file
[`Universes`](Universes.html). The Agda keyword
[`open`](https://agda.readthedocs.io/en/latest/language/module-system.html)
asks to make all definitions in the file `Universe` visible in our
file here.

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

  1. The property is a function `A : 𝟙 → 𝓤` for some universe `𝓤`.

  1. The type `A(x)`, which we will write simply `A x`, doesn't need
     to be a [truth value](HoTT-UF-Agda.html#subsingletonsandsets).
     It can be any type. We will meet examples shortly.

  1. In MLTT, mathematical statements are types, such as

     > `Π (A : 𝟙 → 𝓤), A ⋆ → Π (x : 𝟙), A x`.

  1. We read this in natural language as "for any given property `A`
     of elements of the type `𝟙`, if `A ⋆` holds, then it follows that
     `A x` holds for all `x : 𝟙`".


  1. In Agda, the above type is written as

     > `(A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x`.

     This is the type of functions with three arguments `A : 𝟙 → 𝓤 ̇` &nbsp;
     and `a : A ⋆` and `x : 𝟙`, with values in the type `A x`.

  1. A proof of a mathematical statement rendered as a type is a
     construction of an element of the type.  In our example, we have
     to construct a function, which we will name `𝟙-induction`.

We do this as follows in Agda, where we first declare the type of the
function `𝟙-induction` with "`:`" and then define the function by an
equation:

\begin{code}
𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a
\end{code}

The universe `𝓤` is arbitrary, and Agda knows `𝓤` is a universe variable because we [said so above](HoTT-UF-Agda.html#universes).

Notice that we supply `A` and `a` as arbitrary arguments, but instead of
an arbitrary `x : 𝟙` we have written "`⋆`". Agda accepts this because it
knows from the definition of `𝟙` that "`⋆`" is the only element of the
type `𝟙`. This mechanism is called *pattern matching*.

A particular case of `𝟙-induction` occurs when the family `A` is constant
with value `B`, which can be written variously as

   > `A x = B`

or

   > `A = λ (x : 𝟙) → B`,

or

   > `A = λ x → B`

if we want Agda to figure out the type of `x` by itself, or

   > `A = λ _ → B`

if we don't want to name the argument of `A` because it
is not used. In usual mathematical practice, such a [lambda expression](https://plato.stanford.edu/entries/lambda-calculus/) is [often
written](https://en.wikipedia.org/wiki/Function_(mathematics)#Arrow_notation)

   > `x ↦ B` (`x` is mapped to `B`)

so that the above amount to `A = (x ↦ B)`.

Given a type `B` and a point `b : B`, we construct the function `𝟙 → B`
that maps any given `x : 𝟙` to `b`.

\begin{code}
𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x
\end{code}

The above expression `B → (𝟙 → B)` can be written as `B → 𝟙 → B`,
omitting the brackets, as the function-type formation symbol `→` is
taken to be right associative.

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

This means that when we write

   > `!𝟙 x`

we have to recover the (uniquely determined) missing type `X` with `x : X`
"from the context". When Agda can't figure it out, we need to
supply it and write

   > `!𝟙 {𝓤} {X} x`.

This is because `𝓤` is also an implicit argument (all things declared
with the Agda keyword *variable* [as
above](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html#universes)
are implicit arguments). There are other,
[non-positional](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html),
ways to indicate `X` without having to indicate `𝓤` too. Occasionally,
people define variants of a function with different choices of
"implicitness", as above.

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
𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
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
is the [number of permutations](https://en.wikipedia.org/wiki/Factorial)
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
we will be able to show that "(*false* → *true*) `≡` *true*", which amounts
to `(𝟘 → 𝟙) ≡ 𝟙`, which in turn says that there is precisely one function
`𝟘 → 𝟙`, namely the (vacuous) function.

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
role in the Agda development of these lecture notes.

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

The definition of `ℕ-induction` is itself by induction. It says that given a point

   > `a₀ : A 0`

and a function

   > `f : (n : ℕ) → A n → A (succ n)`,

in order to calculate an element of `A n` for a given `n : ℕ`, we just calculate `h n`, that is,

   > `f n (f (n-1) (f (n-2) (... (f 0 a₀)...)))`.

So the principle of induction is a construction that given a *base
case* `a₀ : A 0`, an *induction step* `f : (n : ℕ) → A n → A (succ n)`
and a number `n`, says how to get an element of the type `A n` by
[primitive
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

  _+_  _×_ : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_
\end{code}

The above "fixity" declarations allow us to indicate the precedences
(multiplication has higher precedence than addition) and their
associativity (here we take left-associativity as the convention, so that
e.g. `x+y+z` parses as `(x+y)+z`).

Equivalent definitions use `ℕ-induction` on the second argument `y`, via
`ℕ-iteration`:

\begin{code}
module Arithmetic' where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_
\end{code}

Here the expression "`x +_`" stands for the function `ℕ → ℕ` that adds
`x` to its argument. So to multiply `x` by `y`, we apply `y` times the
function "`x +_`" to `0`.

As another example, we define the less-than-or-equal relation by
nested induction, on the first argument and then the second, but we
use pattern
matching for the sake of readability.

*Exercise*. [Write it](HoTT-UF-Agda.html#someexercisessol) using
`ℕ-induction`, recursion or iteration, as appropriate.

\begin{code}
module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x
\end{code}

*Exercise*. After learning [`Σ`](HoTT-UF-Agda.html#sigmatypes)
 and [`_≡_`](HoTT-UF-Agda.html#identitytype) explained below, prove [that](HoTT-UF-Agda.html#BasicArithmetic)

   > `x ≤ y` if and only if `Σ \(z : ℕ) → x + z ≡ y`.

Later, after learning
[univalence](HoTT-UF-Agda.html#univalence) prove that in this case
[this implies](HoTT-UF-Agda.html#additionalexercisessol)

   > `(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`.

That [bi-implication can be turned into
equality](HoTT-UF-Agda.html#univalence-gives-propext) only holds for
types that are subsingletons (and this is called [propositional extensionality](HoTT-UF-Agda.html#propext)).

If we are doing applied mathematics and want to actually compute, we
can define a type for binary notation for the sake of efficiency, and
of course people have done [that](https://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html).
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
prove that `A (inl x)` holds for all `x : X` and that `A (inr y)` holds for
all `y : Y`. This amounts to definition by cases:

\begin{code}
+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z

+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)
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
of the `Σ` syntax:

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
will call these two fields `x` and `y` something like `pr₁` and `pr₂`,
or `fst` and `snd`, for first and second projection, rather than `x`
and `y`, and then do `open Σ public` and have the projections
available as functions automatically. But we will deliberately not do
that, and instead define the projections ourselves, because this is
confusing for beginners, no matter how mathematically or
computationally versed they may be, in particular because it will not
be immediately clear that the projections have the following types.

\begin{code}
pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y
\end{code}

To prove that `A z` holds for all `z : Σ Y`, for a given
property `A`, we just prove that we have `A (x , y)` for all `x :
X` and `y : Y x`.  This is called `Σ` induction or `Σ`
elimination, or `uncurry`, after [Haskell
Curry](https://en.wikipedia.org/wiki/Haskell_Curry).
\begin{code}
Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A (x , y))
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

  1. The binary cartesian product represents conjunction "and". If the
     types `A` and `B` stand for mathematical statements, then the
     mathematical statement

       > `A` and `B`

     is codified as

       > `A × B`,

     because to establish "`A` and `B`", we have to provide a
     pair `(a , b)` of proofs `a : A` and `b : B`.

     So notice that in type theory proofs are mathematical objects,
     rather than meta-mathematical entities like in set theory. They
     are just elements of types.

  1. The more general type

       > `Σ (x : X), A x`,

     if the type `X` stands for a mathematical object and `A` stands for a mathematical
     statement, represents *designated* existence

       > there is a designated `x : X` with `A x`.

     To establish this, we have to provide a specific element `x : X`
     and a proof `a : A x`, together in a pair `(x , a)`.

  1. Later we will discuss *unspecified* existence


       > `∃ (x : X), A x`,

     which will be obtained by a sort of quotient of `Σ (x : X), A x`,
     written

       > `∥ Σ (x : X), A x ∥`,

     that identifies all the elements of the type `Σ (x : X), A x` in
     a single equivalence class, called its subsingleton (or truth
     value or propositional) [truncation](HoTT-UF-Agda.html#truncation).

  1. Another reading of

       > `Σ (x : X), A x`

     is as

       > the type of `x : X` with `A x`,

     similar to set-theoretical notation

       > `{ x ∈ X | A x }`.

     But we
     have to be careful because if there is more than one element
     in the type `A x`, then `x` will occur more than once in this
     type. More precisely, for `a₀ a₁ : A x` we have inhabitants
     `(x , a₀)` and `(x , a₁)` of the type `Σ (x : X), A x`.

     In such situations, if we don't want that, we have to be
     careful and either ensure that the type `A x` has at most one
     element for every `x : X`, or instead consider the truncated type
     `∥ A x ∥` and write

       > `Σ (x : X), ∥ A x ∥`.

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
being able to prove that the only element of the type `Id X x x` would
be `refl x`, or that the type `Id X x y` would have at most one
element no matter what `y : X` is.

There is however, one interesting, and crucial, thing we [can
prove](HoTT-UF-Agda.html#singleton-type), namely that for any fixed
element `x : X`, the type


   > `Σ \(y : Y) → Id X x y`

is always a [singleton](HoTT-UF-Agda.html#hlevel).

We will use the following alternative notation for the identity type
former `Id`, where the symbol "`_`" in the right-hand side of the
definition indicates that we ask Agda to infer which type we are
talking about (which is `X`, but this name is not available in the
scope of the *defining equation* of the type former `_≡_`):

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

However, for the elements of *some* types, such as the type `ℕ` of
natural numbers, it is [possible to
prove](HoTT-UF-Agda.html#naturalsset) that any identity type `x ≡ y`
has at most one element. Such types are called [sets in univalent
mathematics](HoTT-UF-Agda.html#subsingletonsandsets).

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

A possible way to understand the element `refl x` of the type `x ≡ x`
is as the "generic identification" between the point `x` and itself,
but which is by no means necessarily the *only* identitification in
univalent foundations. It is generic in the sense that to explain what
happens with all identifications `p : x ≡ y` between any two points
`x` and `y` of a type `X`, it suffices to explain what happens with
the identification `refl x : x ≡ x` for all points `x : X`. This is
what the induction principle for identity given by Martin-Löf says,
which he called `J` (we could have called it `≡-induction`, but we
prefer to honour MLTT tradition):

\begin{code}
J : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p

J X A f x x (refl x) = f x
\end{code}

This is [related](https://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html) to the [Yoneda
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
on `refl`). This is [harder](http://www.cse.chalmers.se/~coquand/singl.pdf).

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

In the proof of the following, we are given hypothetical
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

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (Y → X)
rl-implication = pr₂
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
Id→Fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))
\end{code}

Here the identity function is that of the universe `𝓤` where the types
`X` and `Y` live. An equivalent definition is the following, where
this time the identity function is that of the type `X`:

\begin{code}
Id→Fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→Fun' (refl X) = 𝑖𝑑 X

Id→Funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
              → Id→Fun p ≡ Id→Fun' p

Id→Funs-agree (refl X) = refl (𝑖𝑑 X)
\end{code}

So if we have a hypothetical identification `p : 𝟙 ≡ 𝟘`, then we get a
function `𝟙 → 𝟘`. We apply this function to `⋆ : 𝟙` to conclude the
proof.

\begin{code}
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p ⋆
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
decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : (X : 𝓤 ̇ ) → 𝓤 ̇
has-decidable-equality X = (x y : X) → decidable (x ≡ y)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
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
`not-zero-is-one` with such outrageous arguments. The other case `n =
₁` doesn't need to use the hypothesis `f : ₁ ≡ ₀ → 𝟘`, because the
desired conclusion holds right away, as it is `₁ ≡ ₁`, which is proved
by `refl ₁`. But notice that there is nothing wrong with the
hypothesis `f : ₁ ≡ ₀ → 𝟘`. For example, we can use `not-zero-is-one`
taking `n` to be `₀` and `f` to be `₁-is-not-₀`, so that the
hypotheses can be fulfilled in the second equation.

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

If `P or Q` holds and `P` fails, then `Q` holds:

\begin{code}

right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
right-fails-gives-left-holds (inl p) u = p
right-fails-gives-left-holds (inr q) u = !𝟘 _ (u q)

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
 twin-prime-conjecture = (n : ℕ) → Σ \(p : ℕ) → (p ≥ n)
                                              × is-prime p
                                              × is-prime (p ∔ 2)
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
`ℕ` has decidable equality:

\begin{code}
ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : decidable (x ≡ y) → decidable (succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))
\end{code}

*Exercise*. Students should do this kind of thing at least once in
their academic life: rewrite the above proof of the decidability of
equality of `ℕ` to use the `ℕ-induction` principle instead of pattern
matching and recursion, to understand by themselves that this can be
done.

We now move to basic arithmetic, and we use a module for that.

\begin{code}
module basic-arithmetic-and-order where

  open ℕ-order public
  open Arithmetic renaming (_+_ to _∔_) hiding (_×_)
\end{code}

We can show that addition is associative as follows, by induction on
`z`, where `IH` stands for "induction hypothesis":

\begin{code}
  +-assoc : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)

  +-assoc x y zero     = (x ∔ y) ∔ 0 ≡⟨ refl _ ⟩
                         x ∔ (y ∔ 0) ∎

  +-assoc x y (succ z) = (x ∔ y) ∔ succ z   ≡⟨ refl _     ⟩
                         succ ((x ∔ y) ∔ z) ≡⟨ ap succ IH ⟩
                         succ (x ∔ (y ∔ z)) ≡⟨ refl _     ⟩
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
illustration (the author of these notes can write, but not read it the
absence of the above verbose version):

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

  +-base-on-first (succ x) = 0 ∔ succ x   ≡⟨ refl _     ⟩
                             succ (0 ∔ x) ≡⟨ ap succ IH ⟩
                             succ x       ∎
   where
    IH : 0 ∔ x ≡ x
    IH = +-base-on-first x


  +-step-on-first : (x y : ℕ) → succ x ∔ y ≡ succ (x ∔ y)

  +-step-on-first x zero     = refl (succ x)

  +-step-on-first x (succ y) = succ x ∔ succ y   ≡⟨ refl _     ⟩
                               succ (succ x ∔ y) ≡⟨ ap succ IH ⟩
                               succ (x ∔ succ y) ∎
   where
    IH : succ x ∔ y ≡ succ (x ∔ y)
    IH = +-step-on-first x y
\end{code}

Using this, the commutativity of addition can be proved by induction on the first argument.

\begin{code}
  +-comm : (x y : ℕ) → x ∔ y ≡ y ∔ x

  +-comm 0 y = 0 ∔ y ≡⟨ +-base-on-first y ⟩
               y     ≡⟨ refl _ ⟩
               y ∔ 0 ∎

  +-comm (succ x) y = succ x ∔ y  ≡⟨ +-step-on-first x y ⟩
                      succ(x ∔ y) ≡⟨ ap succ IH          ⟩
                      succ(y ∔ x) ≡⟨ refl _              ⟩
                      y ∔ succ x  ∎
    where
     IH : x ∔ y ≡ y ∔ x
     IH = +-comm x y
\end{code}

We now show that addition is cancellable in its left argument, by
induction on the left argument:

\begin{code}
  +-lc : (x y z : ℕ) → x ∔ y ≡ x ∔ z → y ≡ z

  +-lc 0        y z p = y     ≡⟨ (+-base-on-first y)⁻¹ ⟩
                        0 ∔ y ≡⟨ p                     ⟩
                        0 ∔ z ≡⟨ +-base-on-first z     ⟩
                        z     ∎

  +-lc (succ x) y z p = IH
   where
    q = succ (x ∔ y) ≡⟨ (+-step-on-first x y)⁻¹ ⟩
        succ x ∔ y   ≡⟨ p                       ⟩
        succ x ∔ z   ≡⟨ +-step-on-first x z     ⟩
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
             succ (x ∔ z) ≡⟨ ap succ p           ⟩
             succ y       ∎)


  ≼-gives-≤ : (x y : ℕ) → x ≼ y → x ≤ y

  ≼-gives-≤ 0 0               (z , p) = ⋆

  ≼-gives-≤ 0 (succ y)        (z , p) = ⋆

  ≼-gives-≤ (succ x) 0        (z , p) = positive-not-zero (x ∔ z) q
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p                       ⟩
        zero         ∎

  ≼-gives-≤ (succ x) (succ y) (z , p) = IH
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p                       ⟩
        succ y       ∎

    IH : x ≤ y
    IH = ≼-gives-≤ x y (z , succ-lc q)
\end{code}

[Later](HoTT-UF-Agda.html#additionalexercisesswol) we will show that
`(x ≤ y) ≡ Σ \(z : ℕ) → x + z ≡ y`, using univalence.

We now develop some generally useful material regarding the order `≤`
on natural numbers. First, it is reflexive, transitive and antisymmetric:

\begin{code}
  ≤-refl : (n : ℕ) → n ≤ n
  ≤-refl zero     = ⋆
  ≤-refl (succ n) = ≤-refl n

  ≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
  ≤-trans zero m n p q = ⋆
  ≤-trans (succ l) zero n p q = !𝟘 (succ l ≤ n) p
  ≤-trans (succ l) (succ m) zero p q = q
  ≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

  ≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
  ≤-anti zero zero p q = refl zero
  ≤-anti zero (succ n) p q = !𝟘 (zero ≡ succ n) q
  ≤-anti (succ m) zero p q = !𝟘 (succ m ≡ zero) p
  ≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

  ≤-succ : (n : ℕ) → n ≤ succ n
  ≤-succ zero     = ⋆
  ≤-succ (succ n) = ≤-succ n

  zero-minimal : (n : ℕ) → zero ≤ n
  zero-minimal n = ⋆

  unique-minimal : (n : ℕ) → n ≤ zero → n ≡ zero
  unique-minimal zero p = refl zero
  unique-minimal (succ n) p = !𝟘 (succ n ≡ zero) p

  ≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ≡ succ n)
  ≤-split zero n l = inl l
  ≤-split (succ m) zero l = inr (ap succ (unique-minimal m l))
  ≤-split (succ m) (succ n) l = +-recursion inl (inr ∘ ap succ) (≤-split m n l)

  _<_ : ℕ → ℕ → 𝓤₀ ̇
  x < y = succ x ≤ y

  not-less-bigger-or-equal : (m n : ℕ) → ¬(n < m) → m ≤ n
  not-less-bigger-or-equal zero n u = zero-minimal n
  not-less-bigger-or-equal (succ m) zero = dni (zero < succ m) (zero-minimal m)
  not-less-bigger-or-equal (succ m) (succ n) = not-less-bigger-or-equal m n

  bounded-∀-next : (A : ℕ → 𝓤 ̇ ) (k : ℕ)
                 → A k
                 → ((n : ℕ) → n < k → A n)
                 → (n : ℕ) → n < succ k → A n
  bounded-∀-next A k a φ n l = +-recursion f g s
   where
    s : (n < k) + (succ n ≡ succ k)
    s = ≤-split (succ n) k l

    f : n < k → A n
    f = φ n

    g : succ n ≡ succ k → A n
    g p = transport A ((succ-lc p)⁻¹) a
\end{code}

The type of roots of a function:

\begin{code}
  root : (ℕ → ℕ) → 𝓤₀ ̇
  root f = Σ \(n : ℕ) → f n ≡ 0

  _has-no-root<_ : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  f has-no-root< k = (n : ℕ) → n < k → f n ≢ 0
\end{code}

The type of minimal roots of a function:

\begin{code}
  minimal-root : (ℕ → ℕ) → 𝓤₀ ̇
  minimal-root f = Σ \(m : ℕ) → (f m ≡ 0)
                              × (f has-no-root< m)

  minimal-root-is-root : ∀ f → minimal-root f → root f
  minimal-root-is-root f (m , p , _) = m , p

  bounded-ℕ-search : ∀ k f → (minimal-root f) + (f has-no-root< k)
  bounded-ℕ-search zero f = inr (λ n → !𝟘 (f n ≢ 0))
  bounded-ℕ-search (succ k) f = +-recursion φ γ (bounded-ℕ-search k f)
   where
    A : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
    A k f = (minimal-root f) + (f has-no-root< k)

    φ : minimal-root f → A (succ k) f
    φ = inl

    γ : f has-no-root< k → A (succ k) f
    γ u = +-recursion γ₀ γ₁ (ℕ-has-decidable-equality (f k) 0)
     where
      γ₀ : f k ≡ 0 → A (succ k) f
      γ₀ p = inl (k , p , u)

      γ₁ : f k ≢ 0 → A (succ k) f
      γ₁ v = inr (bounded-∀-next (λ n → f n ≢ 0) k v u)
\end{code}

Given any root, we can find a minimal root.

\begin{code}
  bounded-search-ℕ-minimal-root : ∀ f n → f n ≡ 0 → minimal-root f
  bounded-search-ℕ-minimal-root f n p = γ
   where
    g : ¬(f has-no-root< (succ n))
    g φ = φ n (≤-refl n) p

    γ : minimal-root f
    γ = right-fails-gives-left-holds (bounded-ℕ-search (succ n) f) g
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="uminagda"></a> Univalent Mathematics in Agda

### <a id="axiomaticutt"></a> Our univalent type theory

  * A spartan MLTT [as above](HoTT-UF-Agda.html#spartanmltt).
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
### <a id="subsingletonsandsets"></a> Singletons, subsingletons and sets

#### <a id="singleton-types"></a> Singleton (or contractible) types

Voevodsky defined a notion of *contractible type*, which we
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

Once we have defined the notion of [type
equivalence](HoTT-UF-Agda.html#fibersandequivalences), we will have
that a type is a singleton if and only if it is equivalent to `𝟙`.

When working with singleton types, it will be convenient to have
distinguished names for the two projections:

\begin{code}
center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ
\end{code}

#### <a id="subsingleton-types"></a> Subsingletons (or propositions or truth values)

A type is a subsingleton if it has at most one element, that is, any
two of its elements are equal, or identified.

\begin{code}
is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y     ⟩
                                             y ∎

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ )
                                     → X → is-subsingleton X → is-singleton X

pointed-subsingletons-are-singletons X x s = (x , s x)


singleton-iff-pointed-and-subsingleton : {X : 𝓤 ̇ }
                                       → is-singleton X ⇔ (X × is-subsingleton X)

singleton-iff-pointed-and-subsingleton {𝓤} {X} = (a , b)
 where
  a : is-singleton X → X × is-subsingleton X
  a s = center X s , singletons-are-subsingletons X s

  b : X × is-subsingleton X → is-singleton X
  b (x , t) = pointed-subsingletons-are-singletons X x t
\end{code}

The terminology stands for *[subtype](HoTT-UF-Agda.html#subtypes-of)
of a singleton* and is
[justified](HoTT-UF-Agda.html#the-subsingletons-are-the-subtypes-of-a-singleton)
by the fact that a type `X` is a subsingleton according to the above
definition if and only if the map `X → 𝟙` is an
[embedding](HoTT-UF-Agda.html#embeddings), if and only if `X` is
embedded into a singleton.

Under [univalent excluded
middle](HoTT-UF-Agda.html#em), the empty type `𝟘` and the singleton
type `𝟙` are the only subsingletons, up to equivalence, or up to
identity if we further assume univalence.

Subsingletons are also called propositions or truth values:

\begin{code}
is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop        = is-subsingleton
is-truth-value = is-subsingleton
\end{code}

The terminology `is-subsingleton` is more mathematical and avoids the
clash with the slogan [propositions as
types](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence),
which is based on the interpretation of mathematical statements as
arbitrary types, rather than just subsingletons. In these notes we
prefer the terminology *subsingleton*, but we occasionally use the
terminologies *proposition* and *truth value*. When we wish to
emphasize this notion of proposition adopted in univalent mathematics,
as opposed to "propositions as (arbitrary) types", we may say
*univalent proposition*.

In some formal systems, for example set theory based on first-order
logic, one can tell that something is a proposition by looking at its
syntactical form, e.g. "there are infinitely many prime numbers" is a
proposition, by construction, in such a theory.

In univalent mathematics, however, propositions are mathematical,
rather than meta-mathematical, objects, and the fact that a type turns
out to be a proposition requires mathematical proof.  Moreover, such a
proof may be subtle and not immediate and require significant
preparation. An [example](HoTT-UF-Agda.html#univalencesubsingleton) is
the proof that the univalence axiom is a proposition, which relies on
the fact that univalence [implies](HoTT-UF-Agda.html#funextfromua)
function extensionality, which in turn
[implies](HoTT-UF-Agda.html#being-equiv-is-subsingleton) that the
statement that a map is an equivalence is a proposition. Another
non-trivial example, which again relies on univalence or at least
function extensionality, is the proof that the statement that a type
`X` is a proposition [is itself a
proposition](HoTT-UF-Agda.html#being-subsingleton-is-subsingleton),
which can be written as `is-prop (is-prop X)`.

#### <a id="set-types"></a> Sets

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
### <a id="em"></a> Univalent excluded middle

As mentioned above, under excluded middle, the only two subsingletons,
up to equivalence, are `𝟘` and `𝟙`. In fact, excluded middle in
univalent mathematics says precisely that.

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
statement (it can't be proved or disproved). We will deliberately keep
it undecided, adopting a neutral approach to the constructive
vs. non-constructive dichotomy. We will however prove a couple of
consequences of excluded middle in discussions of foundational issues
such as size and existence of subsingleton truncations. We will also
prove that excluded middle is a consequence of the axiom of choice.

It should be emphasized that the potential failure of excluded middle
doesn't say that there may be mysterious subsingletons that fail to be
singletons and also fail to be empty. No such things occur in
mathematical nature:

\begin{code}
no-unicorns : ¬(Σ \(X : 𝓤 ̇ ) → is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , i , f , g) = c
 where
  e : is-empty X
  e x = f (pointed-subsingletons-are-singletons X x i)

  c : 𝟘
  c = g e
\end{code}

Given this, what does the potential failure of excluded middle *mean*?
That there is no general way to *determine which of the two cases*
`is-singleton X` and `is-empty X` applies for a given subsingleton
`X`. This kind of phenomenon should be familiar even in classical,
non-constructive mathematics: although we are entitled to believe that
the Goldblach conjecture either holds or fails, we still don't know
which one is the case, despite efforts by the sharpest mathematical
minds. A hypothetical element of the type `EM` would, in particular,
be able to solve the Goldbach conjecture. There is nothing wrong or
contradictory with assuming the existence of such a magic box. There
is only loss of the implicit algorithmic character of our type theory,
which most mathematicians will be perfectly happy to live with. In
these notes we don't advocate any particular philosophy for or against
excluded middle and other non-constructive principles. We confine
ourselves to discussing facts.

*Exercise*. We also have that it is impossible for `is-singleton X +
is-empty X` to fail for a given subsingleton `X`, which amounts to
saying that

   > `¬¬(is-singleton X + is-empty X)`

always holds.

Occasionaly one hears people asserting that this says that the double
negation of excluded middle holds. But this is incorrect. The above
statement, when written in full, is

   > `(X : 𝓤 ̇ ) → is-subsingleton X → ¬¬(is-singleton X + is-empty X)`.

This is a theorem, which is quite different from the double negation
of excluded middle, which is not a theorem and is

   > `¬¬((X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X)`.

Just as excluded middle, this is an independent statement.

*Exercise*. Continued from the previous exercise. Also for any type
`R` replacing the empty type, there is a function `((X + (X → R)) → R)
→ R`, so that the kind of phenomenon illustrated in the previous
exercise has little to do with the emptiness of the empty type.


[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="magmasandmonoids"></a> The types of magmas and monoids

A [magma](https://en.wikipedia.org/wiki/Magma_(algebra)) is a *set* equipped with a binary operation subject to no laws
[[Bourbaki](https://books.google.co.uk/books?id=STS9aZ6F204C&pg=PA1&redir_esc=y#v=onepage&q&f=false)].  We can define the type of magmas in a universe `𝓤` as follows:

\begin{code}
module magmas where

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

The following function [will be](HoTT-UF-Agda.html#sns) a bijection in the presence of
univalence, so that the identifications of magmas are in one-to-one
correspondence with the magma isomorphisms:

\begin{code}
 magma-Id→iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
 magma-Id→iso p = (⌜ p ⌝ , ⌜⌝-is-iso p )
\end{code}

If we omit the sethood condition in the definition of the type of
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
module monoids where

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
 Monoid 𝓤 = Σ \(X : 𝓤 ̇ )
          → is-set X
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
drop the sethood requirement, then the equations can hold in multiple
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

*Exercise*. Define the type of [groups](https://en.wikipedia.org/wiki/Group_(mathematics)) (with sets as carriers).

*Exercise*. Write down the various types of
[categories](https://en.wikipedia.org/wiki/Category_(mathematics))
defined in the HoTT book in Agda.

*Exercise*. Try to define a type of [topological
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

*Exercise*. Try to do this with `J` and with `H`.

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
sense that it preserves the neutral element and commutes with
composition:

\begin{code}
ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)

ap-refl f x = refl (refl (f x))


ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q

ap-∙ f p (refl y) = refl (ap f p)
\end{code}

Notice that we also have

\begin{code}
ap⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ≡ y)
     → (ap f p)⁻¹ ≡ ap f (p ⁻¹)

ap⁻¹ f (refl x) = refl (refl (f x))
\end{code}

The above functions `ap-refl` and `ap-∙` constitute functoriality in
the second argument. We also have functoriality in the first argument,
in the following sense:

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
order, but identification composition in the diagramatic order (as is
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
                 → {x y : X} (p : x ≡ y)
                 → τ y ∘ transport A p ≡ transport B p ∘ τ x

Nats-are-natural A B τ (refl x) = refl (τ x)
\end{code}

We will have the opportunity to use the following constructions a
number of times:

\begin{code}
NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)


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
[two-point type](HoTT-UF-Agda.html#binarysum) `𝟙 + 𝟙` with elements `₀` and
`₁`.  But there will be two identifications `p₀ p₁ : Color ≡ 𝟚`, one
that identifies `Black` with `₀` and `White` with `₁`, and another one
that identifies `Black` with `₁` and `White` with `₀`. There is no
preferred coding of binary colors as bits.  And, precisely because of
that, even if univalence does give inhabitants of the type `Color ≡
𝟚`, it doesn't make sense to ask whether `Black ≡ ₀` holds without
specifying one of the possible inhabitants `p₀` and `p₁`.

What we will have is that the functions `transport id p₀` and
`transport id p₁` are the two possible bijections `Color → 𝟚` that
identify colors with bits. So, it is not enough to have `Color ≡ 𝟚` to
be able to compare a color `c : Color` with a bit `b : 𝟚`. We need to
specify which identification `p : Color ≡ 𝟚` we want to consider for
the comparison.  The [same considerations](HoTT-UF-Agda.html#notsets)
apply when we consider identifications `p : 𝟚 ≡ 𝟚`.

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

This is again a non-sensical mathematical statement, because the types
`A x` and `A y` are not the same, but only identified, and in general
there can be many identifications, not just `ap A p`, and so any
identification between elements of `A x` and `A y` has to be with
respect to a specific identification, as in the above particular case.

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
equivalence in at most one way.

The following special case of `to-Σ-≡` is often useful:

\begin{code}
to-Σ-≡' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {x : X} {a a' : A x}
        → a ≡ a' → Id (Σ A) (x , a) (x , a')

to-Σ-≡' {𝓤} {𝓥} {X} {A} {x} = ap (λ - → (x , -))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="hlevel"></a> Voevodsky's notion of hlevel

Voevodsky's hlevels `0,1,2,3,...` are shifted by `2` with respect to
the `n`-groupoid numbering convention, and correspond to `-2`-groupoids
(singletons), `-1`-groupoids (subsingletons), `0`-groupoids (sets),...

The hlevel relation is defined by induction on `ℕ`, with the
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

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="hedberg"></a> Hedberg's Theorem

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
both start with the letter "`w`".

We first define the type of constant endomaps of a given type:

\begin{code}
wconstant-endomap : 𝓤 ̇ → 𝓤 ̇
wconstant-endomap X = Σ \(f : X → X) → wconstant f

wcmap : (X : 𝓤 ̇ ) → wconstant-endomap X → (X → X)
wcmap X (f , w) = f

wcmap-constancy : (X : 𝓤 ̇ ) (c : wconstant-endomap X)
                → wconstant (wcmap X c)
wcmap-constancy X (f , w) = w
\end{code}

The point is that a type is a set if and only if its identity types
all have designated `wconstant` endomaps:

\begin{code}
Hedberg : {X : 𝓤 ̇ } (x : X)
        → ((y : X) → wconstant-endomap (x ≡ y))
        → (y : X) → is-subsingleton (x ≡ y)

Hedberg {𝓤} {X} x c y p q =
 p                       ≡⟨ a y p                                     ⟩
 f x (refl x)⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 f x (refl x)⁻¹ ∙ f y q  ≡⟨ (a y q)⁻¹                                 ⟩
 q                       ∎
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = wcmap (x ≡ y) (c y)

  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = wcmap-constancy (x ≡ y) (c y)

  a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
  a x (refl x) = (⁻¹-left∙ (f x (refl x)))⁻¹
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="setscharacterization"></a> A characterization of sets

The following is immediate from the definitions:

\begin{code}
wconstant-≡-endomaps : 𝓤 ̇ → 𝓤 ̇
wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)

sets-have-wconstant-≡-endomaps : (X : 𝓤 ̇ ) → is-set X → wconstant-≡-endomaps X
sets-have-wconstant-≡-endomaps X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p

  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q
\end{code}

And the converse is the content of Hedberg's Theorem.

\begin{code}
types-with-wconstant-≡-endomaps-are-sets : (X : 𝓤 ̇ )
                                         → wconstant-≡-endomaps X → is-set X
types-with-wconstant-≡-endomaps-are-sets X c x = Hedberg x
                                                  (λ y → wcmap (x ≡ y) (c x y) ,
                                                   wcmap-constancy (x ≡ y) (c x y))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="subsingletonsaresets"></a> Subsingletons are sets

In the following definition of the auxiliary function `f`, we ignore
the argument `p`, using the fact that `X` is a subsingleton instead,
to get a `wconstant` function:

\begin{code}
subsingletons-have-wconstant-≡-endomaps : (X : 𝓤 ̇ )
                                        → is-subsingleton X
                                        → wconstant-≡-endomaps X

subsingletons-have-wconstant-≡-endomaps X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y

  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)
\end{code}

And the corollary is that subsingleton types are sets.
\begin{code}
subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = types-with-wconstant-≡-endomaps-are-sets X
                               (subsingletons-have-wconstant-≡-endomaps X s)
\end{code}

In particular, the types `𝟘` and `𝟙` are sets.

\begin{code}
𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingletons-are-sets 𝟘 𝟘-is-subsingleton

𝟙-is-set : is-set 𝟙
𝟙-is-set = subsingletons-are-sets 𝟙 𝟙-is-subsingleton
\end{code}


[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="hlevel1subsingleton"></a> The types of hlevel 1 are the subsingletons

Then with the above we get our desired characterization of the types of
hlevel `1` as an immediate consequence:

\begin{code}
subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇ )
                              → is-subsingleton X
                              → X is-of-hlevel 1

subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)


types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇ )
                                    → X is-of-hlevel 1
                                    → is-subsingleton X

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
#### <a id="hlevel2set"></a> The types of hlevel 2 are the sets

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
#### <a id="hlevelsupper"></a> The hlevels are upper closed

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

*Exercise*. Formulate and prove the following. The type `𝟙` has
minimal hlevel `0`.

\begin{code}
_has-minimal-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X has-minimal-hlevel 0        = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) × ¬(X is-of-hlevel n)

_has-minimal-hlevel-∞ : 𝓤 ̇ → 𝓤 ̇
X has-minimal-hlevel-∞ = (n : ℕ) → ¬(X is-of-hlevel n)
\end{code}

The type `𝟘` has minimal hlevel `1`, the type `ℕ` has minimal hlevel
`2`. The solution to the fact that `ℕ` has hlevel 2 is given in the
next section. More ambitiously, after
[univalence](HoTT-UF-Agda.html#univalence) is available, show that the
type of monoids has minimal hlevel `3`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="naturalsset"></a> `ℕ` and `𝟚` are sets

If a type has decidable equality we can define a `wconstant`
function `x ≡ y → x ≡ y` and hence conclude that it is a set. This
argument is due to Hedberg.

\begin{code}
pointed-types-have-wconstant-endomap : {X : 𝓤 ̇ } → X → wconstant-endomap X
pointed-types-have-wconstant-endomap x = ((λ y → x) , (λ y y' → refl x))

empty-types-have-wconstant-endomap : {X : 𝓤 ̇ } → is-empty X → wconstant-endomap X
empty-types-have-wconstant-endomap e = (id , (λ x x' → !𝟘 (x ≡ x') (e x)))


decidable-has-wconstant-endomap : {X : 𝓤 ̇ } → decidable X → wconstant-endomap X
decidable-has-wconstant-endomap (inl x) = pointed-types-have-wconstant-endomap x
decidable-has-wconstant-endomap (inr e) = empty-types-have-wconstant-endomap e


hedberg-lemma : {X : 𝓤 ̇ } → has-decidable-equality X → wconstant-≡-endomaps X
hedberg-lemma {𝓤} {X} d x y = decidable-has-wconstant-endomap (d x y)

hedberg : {X : 𝓤 ̇ } → has-decidable-equality X → is-set X
hedberg {𝓤} {X} d = types-with-wconstant-≡-endomaps-are-sets X (hedberg-lemma d)

ℕ-is-set : is-set ℕ
ℕ-is-set = hedberg ℕ-has-decidable-equality

𝟚-is-set : is-set 𝟚
𝟚-is-set = hedberg 𝟚-has-decidable-equality
\end{code}

Notice that excluded middle implies directly that all sets have
decidable equality, so that in its presence a type is a set if and
only if it has decidable equality.

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

Notice that `has-section r` is the type of all sections `(s , η)` of
`r`, which may well be empty. So a point of this type is a designated
section `s` of `r`, together with the datum `η`. Unless the domain of
`r` is a set, this datum is not property, and we may well have an
element `(s , η')` of the type `has-section r` with `η'` distinct from
`η` for the same `s`.

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

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ∼ 𝑖𝑑 X
retract-equation (r , s , η) = η

retraction-has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y)
                       → has-section (retraction ρ)
retraction-has-section (r , h) = h
\end{code}

We have an identity retraction:

\begin{code}
id-◁ : (X : 𝓤 ̇ ) → X ◁ X
id-◁ X = 𝑖𝑑 X , 𝑖𝑑 X , refl
\end{code}

*Exercise*. The identity retraction is by no means the only retraction
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
              r (s x)           ≡⟨ η x             ⟩
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
X ◀ = id-◁ X
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
  η' (x , a) = x , r x (s x a) ≡⟨ to-Σ-≡' (η x a) ⟩
               x , a           ∎
\end{code}

We have that `transport A (p ⁻¹)` is a two-sided inverse of `transport
A p` using the functoriality of `transport A`, or directly by
induction on `p`:

\begin{code}
transport-is-retraction : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                        → transport A p ∘ transport A (p ⁻¹) ∼ 𝑖𝑑 (A y)

transport-is-retraction A (refl x) = refl


transport-is-section : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
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
            r (s y) ≡⟨ η y            ⟩
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

The situation is that we will have a logical equivalence between

  * *data* establishing invertibility of a given function, and

  * the *property* of the function being an equivalence.

Mathematically, what happens is that the type

  * `f` is an equivalence

is a retract of the type

  * `f` is invertible.

This retraction property is not easy to show, and there are many
approaches. We discuss an approach we came up with while developing
these lecture notes, which is intended to be relatively simple and
direct, but the reader should consult other approaches, such as that
of the HoTT book, which has a well-established categorical pedigree.

The problem with the notion of invertibility of `f` is that, while we
have that the inverse `g` is unique when it exists, we cannot in
general prove that the identification data `g ∘ f ∼ id` and `f ∘ g ∼
id` are also unique, and, indeed, [they are not in
general](https://github.com/HoTT/HoTT/blob/master/contrib/HoTTBookExercises.v).

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
                   → f ∘ inverse f e ∼ id

inverse-is-section f e y = fiber-identification (center (fiber f y) (e y))


inverse-centrality : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     (f : X → Y) (e : is-equiv f) (y : Y) (t : fiber f y)
                   → (inverse f e y , inverse-is-section f e y) ≡ t

inverse-centrality f e y = centrality (fiber f y) (e y)


inverse-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                      → inverse f e ∘ f ∼ id

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

The non-trivial direction derives the equivalence property from
invertibility data, for which we use the retraction techniques
explained [above](HoTT-UF-Agda.html#retracts).

Suppose that invertibility data

   > `g : Y → X` ,

   > `η : (x : X) → g (f x) ≡ x`

   > `ε : (y : Y) → f (g y) ≡ y`

for a map `f : X → Y` is given, and that a point `y₀` in the codomain
of `f` is given.

We need to show that the fiber `Σ \(x : X) → f x ≡ y₀` of `y₀` is a
singleton.

  1. We first use the assumption `ε` to show that the type `f (g y) ≡
     y₀` is a retract of the type `y ≡ y₀` for any given `y : Y`.

     To get the section `s : f (g y) ≡ y₀ → y ≡ y₀`, we transport along
     the identification `ε y : f (g y) ≡ y` over the family `A - = (-
     ≡ y₀)`, which can be abbreviated as `_≡ y₀`.

     To get the retraction `r` in the opposite direction, we transport
     along the inverse of the identification `ε y` over the same
     family.

     We already know that this gives a section-retraction pair by
     `transport-is-section`.

  1. Next we have that the type `Σ \(x : X) → f x ≡ y₀` is a retract
     of the type `Σ \(y : Y) → f (g y) ≡ y₀` by `Σ-reindexing-retract`
     using the assumption that `η` exibits `g` as a section of `f`,
     which in turn is a retract of the type `Σ \(y : Y) → y ≡ y₀` by
     applying `Σ` to both sides of the retraction `(f (g y) ≡ y₀) ◁ (y
     ≡ y₀)` of the previous step.

     This amounts to saying that the type `fiber f y₀` is a retract of
     `singleton-type y₀`.

  1. But then we are done, because singleton types are singletons and
     retracts of singletons are singletons.

\begin{code}
invertibles-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → invertible f → is-equiv f

invertibles-are-equivs {𝓤} {𝓥} {X} {Y} f (g , η , ε) y₀ = iii
 where
  i : (y : Y) → (f (g y) ≡ y₀) ◁ (y ≡ y₀)
  i y =  r , s , transport-is-section (_≡ y₀) (ε y)
   where
    s : f (g y) ≡ y₀ → y ≡ y₀
    s = transport (_≡ y₀) (ε y)

    r : y ≡ y₀ → f (g y) ≡ y₀
    r = transport (_≡ y₀) ((ε y)⁻¹)

  ii : fiber f y₀ ◁ singleton-type y₀
  ii = (Σ \(x : X) → f x ≡ y₀)     ◁⟨ Σ-reindexing-retract g (f , η) ⟩
       (Σ \(y : Y) → f (g y) ≡ y₀) ◁⟨ Σ-retract i                    ⟩
       (Σ \(y : Y) → y ≡ y₀)       ◀

  iii : is-singleton (fiber f y₀)
  iii = retract-of-singleton ii (singleton-types-are-singletons Y y₀)


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
to show that [it is a
subsingleton](HoTT-UF-Agda.html#being-equiv-is-subsingleton).

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
            g (f x)           ≡⟨ gf x             ⟩
            x                 ∎

  ε = λ z → f' (f (g (g' z))) ≡⟨ ap f' (fg (g' z)) ⟩
            f' (g' z)         ≡⟨ fg' z             ⟩
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
checking of this file for correctness in the uses of `∘-is-equiv`:

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

Because we have made the above definition abstract, we don't have
access to the given construction when proving things involving
`∘-is-equiv`, such as the contravariance of inversion:

\begin{code}
inverse-of-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               (f : X → Y) (g : Y → Z)
               (i : is-equiv f) (j : is-equiv g)
             → inverse f i ∘ inverse g j ∼ inverse (g ∘ f) (∘-is-equiv j i)

inverse-of-∘ f g i j z =

  f' (g' z)             ≡⟨ (ap (f' ∘ g') (s z))⁻¹                      ⟩
  f' (g' (g (f (h z)))) ≡⟨ ap f' (inverse-is-retraction g j (f (h z))) ⟩
  f' (f (h z))          ≡⟨ inverse-is-retraction f i (h z)             ⟩
  h z                   ∎

 where
  f' = inverse f i
  g' = inverse g j
  h  = inverse (g ∘ f) (∘-is-equiv j i)

  s : g ∘ f ∘ h ∼ id
  s = inverse-is-section (g ∘ f) (∘-is-equiv j i)
\end{code}

The type of equivalences is defined as follows:

\begin{code}
_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f
\end{code}

Notice that this doesn't just say that `X` and `Y` are equivalent: the
type `X ≃ Y` collects all the ways in which the types `X` and `Y` are
equivalent. For example, the two-point type `𝟚` is equivalent to
itself in two ways, by the identity map, and by the map that
interchanges its two points, and hence the type `𝟚 ≃ 𝟚` has two
elements.

Again it is convenient to have special names for its first and second
projections:

\begin{code}
Eq→fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq→fun (f , i) = f

Eq→fun-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (Eq→fun e)
Eq→fun-is-equiv (f , i) = i


invertibility-gives-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → invertible f → X ≃ Y

invertibility-gives-≃ f i = f , invertibles-are-equivs f i
\end{code}

Example:

\begin{code}
Σ-induction-≃ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
              → ((x : X) (y : Y x) → A (x , y)) ≃ ((z : Σ Y) → A z)

Σ-induction-≃ = invertibility-gives-≃ Σ-induction (curry , refl , refl)
\end{code}

The identity equivalence and the composition of two equivalences:

\begin{code}
id-≃ : (X : 𝓤 ̇ ) → X ≃ X
id-≃ X = 𝑖𝑑 X , id-is-equiv X

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
_■ = id-≃
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

Σ-≡-≃ {𝓤} {𝓥} {X} {A}  σ τ = invertibility-gives-≃ from-Σ-≡ (to-Σ-≡ , η , ε)
 where
  η : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  η (refl σ) = refl (refl σ)

  ε : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
    → from-Σ-≡ (to-Σ-≡ w) ≡ w
  ε (refl p , refl q) = refl (refl p , refl q)
\end{code}

Similarly we have:

\begin{code}
to-×-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
       → (pr₁ z ≡ pr₁ t) × (pr₂ z ≡ pr₂ t) → z ≡ t

to-×-≡ (refl x , refl y) = refl (x , y)


from-×-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
         → z ≡ t → (pr₁ z ≡ pr₁ t) × (pr₂ z ≡ pr₂ t)

from-×-≡ {𝓤} {𝓥} {X} {Y} (refl (x , y)) = (refl x , refl y)


×-≡-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (z t : X × Y)
      → (z ≡ t) ≃ (pr₁ z ≡ pr₁ t) × (pr₂ z ≡ pr₂ t)

×-≡-≃ {𝓤} {𝓥} {X} {Y} z t = invertibility-gives-≃ from-×-≡ (to-×-≡ , η , ε)
 where
  η : (p : z ≡ t) → to-×-≡ (from-×-≡ p) ≡ p
  η (refl z) = refl (refl z)

  ε : (q : (pr₁ z ≡ pr₁ t) × (pr₂ z ≡ pr₂ t)) → from-×-≡ (to-×-≡ q) ≡ q
  ε (refl x , refl y) = refl (refl x , refl y)
\end{code}


The following are often useful:

\begin{code}
ap-pr₁-to-×-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ≡ pr₁ t)
              → (p₂ : pr₂ z ≡ pr₂ t)
              → ap pr₁ (to-×-≡ (p₁ , p₂)) ≡ p₁

ap-pr₁-to-×-≡ (refl x) (refl y) = refl (refl x)


ap-pr₂-to-×-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
              → (p₁ : pr₁ z ≡ pr₁ t)
              → (p₂ : pr₂ z ≡ pr₂ t)
              → ap pr₂ (to-×-≡ (p₁ , p₂)) ≡ p₂

ap-pr₂-to-×-≡ (refl x) (refl y) = refl (refl y)


Σ-cong : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B

Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ =
  invertibility-gives-≃ (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε)
 where
  f : (x : X) → A x → B x
  f x = Eq→fun (φ x)

  g : (x : X) → B x → A x
  g x = inverse (f x) (Eq→fun-is-equiv (φ x))

  η : (x : X) (a : A x) → g x (f x a) ≡ a
  η x = inverse-is-retraction (f x) (Eq→fun-is-equiv (φ x))

  ε : (x : X) (b : B x) → f x (g x b) ≡ b
  ε x = inverse-is-section (f x) (Eq→fun-is-equiv (φ x))

  NatΣ-η : (w : Σ A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a) = x , g x (f x a) ≡⟨ to-Σ-≡' (η x a) ⟩
                   x , a           ∎

  NatΣ-ε : (t : Σ B) → NatΣ f (NatΣ g t) ≡ t
  NatΣ-ε (x , b) = x , f x (g x b) ≡⟨ to-Σ-≡' (ε x b) ⟩
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
equivalence `id-≃ X : X ≃ X`. The univalence axiom, for the universe
`𝓤`, says that this canonical map is itself an equivalence.

\begin{code}
Id→Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id→Eq X X (refl X) = id-≃ X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id→Eq X Y)
\end{code}

Thus, the univalence of the universe `𝓤` says that identifications `X
≡ Y` of types in `𝓤` are in canonical bijection with equivalences `X ≃ Y`, if [by
bijection we mean equivalence](HoTT-UF-Agda.html#equivalence-characterization),
where the canonical bijection is
`Id→Eq`.

We emphasize that this doesn't posit that univalence holds. It says
what univalence is (like the type that says what the [twin-prime
conjecture](HoTT-UF-Agda.html#twinprime) is).

\begin{code}
univalence-≃ : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → (X ≡ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)
\end{code}

Here is a third way to [convert a type identification into a
function](HoTT-UF-Agda.html#Id→Fun):

\begin{code}
Id→fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→fun {𝓤} {X} {Y} p = Eq→fun (Id→Eq X Y p)

Id→funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
              → Id→fun p ≡ Id→Fun p
Id→funs-agree (refl X) = refl (𝑖𝑑 X)
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
map that swaps ₀ and ₁:

\begin{code}
swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invertibles-are-equivs
                  swap₂
                  (swap₂ , swap₂-involutive , swap₂-involutive)
\end{code}

We now use a local module to assume univalence of the first universe
in the construction of our example:

\begin{code}
module example-of-a-nonset (ua : is-univalent 𝓤₀) where
\end{code}

The above gives two distinct equivalences:

\begin{code}
 e₀ e₁ : 𝟚 ≃ 𝟚
 e₀ = id-≃ 𝟚
 e₁ = swap₂ , swap₂-is-equiv

 e₀-is-not-e₁ : e₀ ≢ e₁
 e₀-is-not-e₁ p = ₁-is-not-₀ r
  where
   q : id ≡ swap₂
   q = ap Eq→fun p

   r : ₁ ≡ ₀
   r = ap (λ - → - ₁) q
\end{code}

Using univalence, we get two different identifications of the type
`𝟚` with itself:

\begin{code}
 p₀ p₁ : 𝟚 ≡ 𝟚
 p₀ = Eq→Id ua 𝟚 𝟚 e₀
 p₁ = Eq→Id ua 𝟚 𝟚 e₁

 p₀-is-not-p₁ : p₀ ≢ p₁
 p₀-is-not-p₁ q = e₀-is-not-e₁ r
  where
   r = e₀            ≡⟨ (inverse-is-section (Id→Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
       Id→Eq 𝟚 𝟚 p₀  ≡⟨ ap (Id→Eq 𝟚 𝟚) q                               ⟩
       Id→Eq 𝟚 𝟚 p₁  ≡⟨ inverse-is-section (Id→Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₁     ⟩
       e₁            ∎
\end{code}

If the universe `𝓤₀` were a set, then the identifications `p₀` and
`p₁` defined above would be equal, and therefore it is not a set.

\begin{code}
 𝓤₀-is-not-a-set : ¬(is-set (𝓤₀ ̇ ))
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

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="solutions"></a> Formulations

Define functions for the following type declarations. As a matter of
procedure, we suggest to import this file in a solutions file and add
another declaration with the same type and new name
e.g. `sections-are-lc-solution`, because we already have solutions in
this file. It is important not to forget to include the option
`--without-K` in the solutions file that imports (the Agda version of)
this file.

\begin{code}
subsingleton-criterion : {X : 𝓤 ̇ }
                       → (X → is-singleton X)
                       → is-subsingleton X

retract-of-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → Y ◁ X → is-subsingleton X → is-subsingleton Y


left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ≡ f x' → x ≡ x'


lc-maps-reflect-subsingletons : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → left-cancellable f
                              → is-subsingleton Y
                              → is-subsingleton X


has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ \(r : codomain s → domain s) → r ∘ s ∼ id


sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A)
                → has-retraction s → left-cancellable s


equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → has-retraction f


equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-equiv f → has-section f


equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → is-equiv f → left-cancellable f


equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → X ≃ Y
                      → is-subsingleton Y
                      → is-subsingleton X


comp-inverses : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                (f : X → Y) (g : Y → Z)
                (i : is-equiv f) (j : is-equiv g)
                (f' : Y → X) (g' : Z → Y)
              → f' ∼ inverse f i
              → g' ∼ inverse g j
              → f' ∘ g' ∼ inverse (g ∘ f) (∘-is-equiv j i)


equiv-to-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → X ≃ Y
             → is-set Y
             → is-set X


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
been given by André Joyal:

\begin{code}
is-joyal-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f
\end{code}

Provide definitions for the following type declarations:

\begin{code}
one-inverse : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
              (f : X → Y) (r s : Y → X)
            → (r ∘ f ∼ id)
            → (f ∘ s ∼ id)
            → r ∼ s


joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-joyal-equiv f → invertible f


joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-joyal-equiv f → is-equiv f


invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → is-joyal-equiv f


equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g


equiv-to-singleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → X ≃ Y → is-singleton X → is-singleton Y


subtypes-of-sets-are-sets : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                          → left-cancellable m → is-set Y → is-set X


pr₁-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
       → ((x : X) → is-subsingleton (A x))
       → left-cancellable  (λ (t : Σ A) → pr₁ t)


subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                         → is-set X
                         → ((x : X) → is-subsingleton (A x))
                         → is-set (Σ \(x : X) → A x)


pr₁-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → ((x : X) → is-singleton (A x))
          → is-equiv (λ (t : Σ A) → pr₁ t)


pr₁-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-singleton (A x))
      → Σ A ≃ X

pr₁-≃ i = pr₁ , pr₁-equiv i


ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π \(x : X) → Σ \(a : A x) → P x a)
           ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))


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


NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                   (φ : Nat A B)
                                 → is-equiv (NatΣ φ)
                                 → ((x : X) → is-equiv (φ x))


Σ-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → is-subsingleton X
                  → ((x : X) → is-subsingleton (A x))
                  → is-subsingleton (Σ A)


×-is-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-singleton X
                  → is-singleton Y
                  → is-singleton (X × Y)


×-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-subsingleton X
                  → is-subsingleton Y
                  → is-subsingleton (X × Y)

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
#### <a id="solutions"></a> Solutions

For the sake of readability, we re-state the formulations of the
exercises in the type of `sol` in a `where` clause for each exercise.

\begin{code}
subsingleton-criterion = sol
 where
  sol : {X : 𝓤 ̇ } → (X → is-singleton X) → is-subsingleton X
  sol f x = singletons-are-subsingletons (domain f) (f x) x


retract-of-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → Y ◁ X → is-subsingleton X → is-subsingleton Y
  sol (r , s , η) i =  subsingleton-criterion
                        (λ x → retract-of-singleton (r , s , η)
                                (pointed-subsingletons-are-singletons
                                  (codomain s) (s x) i))


lc-maps-reflect-subsingletons = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → left-cancellable f → is-subsingleton Y → is-subsingleton X
  sol f l s x x' = l (s (f x) (f x'))


sections-are-lc = sol
 where
  sol : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A)
      → has-retraction s → left-cancellable s
  sol s (r , ε) {x} {y} p = x       ≡⟨ (ε x)⁻¹ ⟩
                            r (s x) ≡⟨ ap r p  ⟩
                            r (s y) ≡⟨ ε y     ⟩
                            y       ∎


equivs-have-retractions = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f
  sol f e = (inverse f e , inverse-is-retraction f e)


equivs-have-sections = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f
  sol f e = (inverse f e , inverse-is-section f e)


equivs-are-lc = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f
  sol f e = sections-are-lc f (equivs-have-retractions f e)


equiv-to-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-subsingleton Y → is-subsingleton X
  sol (f , i) = lc-maps-reflect-subsingletons f (equivs-are-lc f i)


comp-inverses = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        (f : X → Y) (g : Y → Z)
        (i : is-equiv f) (j : is-equiv g)
        (f' : Y → X) (g' : Z → Y)
      → f' ∼ inverse f i
      → g' ∼ inverse g j
      → f' ∘ g' ∼ inverse (g ∘ f) (∘-is-equiv j i)
  sol f g i j f' g' h k z =
   f' (g' z)                          ≡⟨ h (g' z)               ⟩
   inverse f i (g' z)                 ≡⟨ ap (inverse f i) (k z) ⟩
   inverse f i (inverse g j z)        ≡⟨ inverse-of-∘ f g i j z ⟩
   inverse (g ∘ f) (∘-is-equiv j i) z ∎


equiv-to-set = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-set Y → is-set X
  sol e = subtypes-of-sets-are-sets
            (Eq→fun e)
            (equivs-are-lc (Eq→fun e) (Eq→fun-is-equiv e))


sections-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → has-retraction f → g ∼ f → has-retraction g
  sol f g (r , rf) h = (r ,
                        λ x → r (g x) ≡⟨ ap r (h x) ⟩
                              r (f x) ≡⟨ rf x       ⟩
                              x       ∎)


retractions-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → has-section f → g ∼ f → has-section g
  sol f g (s , fs) h = (s ,
                        λ y → g (s y) ≡⟨ h (s y) ⟩
                              f (s y) ≡⟨ fs y    ⟩
                              y ∎)


one-inverse = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
        (f : X → Y) (r s : Y → X)
      → (r ∘ f ∼ id)
      → (f ∘ s ∼ id)
      → r ∼ s
  sol X Y f r s h k y = r y         ≡⟨ ap r ((k y)⁻¹) ⟩
                        r (f (s y)) ≡⟨ h (s y)        ⟩
                        s y         ∎


joyal-equivs-are-invertible = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-joyal-equiv f → invertible f
  sol f ((s , ε) , (r , η)) = (s , sf , ε)
   where
    sf = λ (x : domain f) → s(f x)       ≡⟨ (η (s (f x)))⁻¹ ⟩
                            r(f(s(f x))) ≡⟨ ap r (ε (f x))  ⟩
                            r(f x)       ≡⟨ η x             ⟩
                            x            ∎

joyal-equivs-are-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-joyal-equiv f → is-equiv f
  sol f j = invertibles-are-equivs f (joyal-equivs-are-invertible f j)


invertibles-are-joyal-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → invertible f → is-joyal-equiv f
  sol f (g , η , ε) = ((g , ε) , (g , η))


equivs-are-joyal-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-equiv f → is-joyal-equiv f
  sol f e = invertibles-are-joyal-equivs f (equivs-are-invertible f e)


equivs-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y}
      → is-equiv f → g ∼ f → is-equiv g
  sol {𝓤} {𝓥} {X} {Y} {f} {g} e h = joyal-equivs-are-equivs g
                                      (retractions-closed-under-∼ f g
                                       (equivs-have-sections f e) h ,
                                      sections-closed-under-∼ f g
                                       (equivs-have-retractions f e) h)


equiv-to-singleton' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → X ≃ Y → is-singleton X → is-singleton Y
  sol e = retract-of-singleton (≃-gives-▷ e)


subtypes-of-sets-are-sets = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
      → left-cancellable m → is-set Y → is-set X
  sol {𝓤} {𝓥} {X} m i h = types-with-wconstant-≡-endomaps-are-sets X c
   where
    f : (x x' : X) → x ≡ x' → x ≡ x'
    f x x' r = i (ap m r)

    κ : (x x' : X) (r s : x ≡ x') → f x x' r ≡ f x x' s
    κ x x' r s = ap i (h (m x) (m x') (ap m r) (ap m s))

    c : wconstant-≡-endomaps X
    c x x' = f x x' , κ x x'

pr₁-lc = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-subsingleton (A x))
      → left-cancellable  (λ (t : Σ A) → pr₁ t)
  sol i p = to-Σ-≡ (p , i _ _ _)


subsets-of-sets-are-sets = sol
 where
  sol : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X
     → ((x : X) → is-subsingleton (A x))
     → is-set (Σ \(x : X) → A x)
  sol X A h p = subtypes-of-sets-are-sets pr₁ (pr₁-lc p) h


pr₁-equiv = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → ((x : X) → is-singleton (A x))
      → is-equiv (λ (t : Σ A) → pr₁ t)
  sol {𝓤} {𝓥} {X} {A} s = invertibles-are-equivs pr₁ (g , η , ε)
   where
    g : X → Σ A
    g x = x , pr₁(s x)

    ε : (x : X) → pr₁ (g x) ≡ x
    ε x = refl (pr₁ (g x))

    η : (σ : Σ A) → g (pr₁ σ) ≡ σ
    η (x , a) = to-Σ-≡ (ε x , singletons-are-subsingletons (A x) (s x) _ a)


ΠΣ-distr-≃ = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
      → (Π \(x : X) → Σ \(a : A x) → P x a)
      ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))
  sol {𝓤} {𝓥} {𝓦} {X} {A} {P} = invertibility-gives-≃ φ (γ , η , ε)
   where
    φ : (Π \(x : X) → Σ \(a : A x) → P x a)
      → Σ \(f : Π A) → Π \(x : X) → P x (f x)
    φ g = ((λ x → pr₁ (g x)) , λ x → pr₂ (g x))

    γ : (Σ \(f : Π A) → Π \(x : X) → P x (f x))
      → Π \(x : X) → Σ \(a : A x) → P x a
    γ (f , φ) x = f x , φ x

    η : γ ∘ φ ∼ id
    η = refl

    ε : φ ∘ γ ∼ id
    ε = refl


Σ-assoc = sol
 where
  sol : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : Σ Y → 𝓦 ̇ }
      → Σ Z ≃ (Σ \(x : X) → Σ \(y : Y x) → Z (x , y))
  sol {𝓤} {𝓥} {𝓦} {X} {Y} {Z} = invertibility-gives-≃ f (g , refl , refl)
   where
    f : Σ Z → Σ \x → Σ \y → Z (x , y)
    f ((x , y) , z) = (x , (y , z))

    g : (Σ \x → Σ \y → Z (x , y)) → Σ Z
    g (x , (y , z)) = ((x , y) , z)


⁻¹-is-equiv : {X : 𝓤 ̇ } (x y : X)
            → is-equiv (λ (p : x ≡ y) → p ⁻¹)
⁻¹-is-equiv x y = invertibles-are-equivs _⁻¹
                   (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive)


⁻¹-≃ = sol
 where
  sol : {X : 𝓤 ̇ } (x y : X) → (x ≡ y) ≃ (y ≡ x)
  sol x y = (_⁻¹ , ⁻¹-is-equiv x y)


singleton-types-≃ = sol
 where
  sol : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x
  sol x = Σ-cong (λ y → ⁻¹-≃ x y)


singletons-≃ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-singleton X → is-singleton Y → X ≃ Y
  sol {𝓤} {𝓥} {X} {Y} i j = invertibility-gives-≃ f (g , η , ε)
   where
    f : X → Y
    f x = center Y j

    g : Y → X
    g y = center X i

    η : (x : X) → g (f x) ≡ x
    η = centrality X i

    ε : (y : Y) → f (g y) ≡ y
    ε = centrality Y j


maps-of-singletons-are-equivs = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-singleton X → is-singleton Y → is-equiv f

  sol {𝓤} {𝓥} {X} {Y} f i j = invertibles-are-equivs f (g , η , ε)
   where
    g : Y → X
    g y = center X i

    η : (x : X) → g (f x) ≡ x
    η = centrality X i

    ε : (y : Y) → f (g y) ≡ y
    ε y = singletons-are-subsingletons Y j (f (g y)) y


logically-equivalent-subsingletons-are-equivalent = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
      → is-subsingleton X → is-subsingleton Y → X ⇔ Y → X ≃ Y
  sol  X Y i j (f , g) = invertibility-gives-≃ f
                          (g ,
                           (λ x → i (g (f x)) x) ,
                           (λ y → j (f (g y)) y))


singletons-are-equivalent = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
      → is-singleton X → is-singleton Y → X ≃ Y
  sol  X Y i j = invertibility-gives-≃ (λ _ → center Y j)
                  ((λ _ → center X i) ,
                   centrality X i ,
                   centrality Y j)


NatΣ-fiber-equiv = sol
 where
  sol : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
      → (x : X) (b : B x) → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
  sol A B φ x b = invertibility-gives-≃ f (g , ε , η)
   where
    f : fiber (φ x) b → fiber (NatΣ φ) (x , b)
    f (a , refl _) = ((x , a) , refl (x , φ x a))

    g : fiber (NatΣ φ) (x , b) → fiber (φ x) b
    g ((x , a) , refl _) = (a , refl (φ x a))

    ε : (w : fiber (φ x) b) → g (f w) ≡ w
    ε (a , refl _) = refl (a , refl (φ x a))

    η : (t : fiber (NatΣ φ) (x , b)) → f (g t) ≡ t
    η ((x , a) , refl _) = refl ((x , a) , refl (NatΣ φ (x , a)))


NatΣ-equiv-gives-fiberwise-equiv = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } (φ : Nat A B)
      → is-equiv (NatΣ φ) → ((x : X) → is-equiv (φ x))
  sol {𝓤} {𝓥} {𝓦} {X} {A} {B} φ e x b = γ
   where
    d : fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)
    d = NatΣ-fiber-equiv A B φ x b

    s : is-singleton (fiber (NatΣ φ) (x , b))
    s = e (x , b)

    γ : is-singleton (fiber (φ x) b)
    γ = equiv-to-singleton d s


Σ-is-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
      → is-subsingleton X
      → ((x : X) → is-subsingleton (A x))
      → is-subsingleton (Σ A)
  sol i j (x , a) (y , b) = to-Σ-≡ (i x y , j y _ _)


×-is-singleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-singleton X
      → is-singleton Y
      → is-singleton (X × Y)
  sol (x , φ) (y , γ) = (x , y) , δ
   where
    δ : ∀ z → x , y ≡ z
    δ (x' , y' ) = to-×-≡ (φ x' , γ y')


×-is-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-subsingleton X → is-subsingleton Y → is-subsingleton (X × Y)
  sol i j = Σ-is-subsingleton i (λ _ → j)


×-is-subsingleton' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → ((Y → is-subsingleton X) × (X → is-subsingleton Y))
      → is-subsingleton (X × Y)
  sol {𝓤} {𝓥} {X} {Y} (i , j) = k
   where
    k : is-subsingleton (X × Y)
    k (x , y) (x' , y') = to-×-≡ (i y x x' , j x y y')


×-is-subsingleton'-back = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-subsingleton (X × Y)
      → (Y → is-subsingleton X) × (X → is-subsingleton Y)
  sol {𝓤} {𝓥} {X} {Y} k = i , j
   where
    i : Y → is-subsingleton X
    i y x x' = ap pr₁ (k (x , y) (x' , y))

    j : X → is-subsingleton Y
    j x y y' = ap pr₂ (k (x , y) (x , y'))


ap₂ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y → Z) {x x' : X} {y y' : Y}
      → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
  sol f (refl x) (refl y) = refl (f x y)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="unicharac"></a> A characterization of univalence

We begin with two general results, which will be placed in a more
general context [later](HoTT-UF-Agda.html#yoneda).

\begin{code}
equiv-singleton-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
                      → (f : (y : X) → x ≡ y → A y)
                      → ((y : X) → is-equiv (f y))
                      → is-singleton (Σ A)

equiv-singleton-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  abstract
   e : (y : X) → (x ≡ y) ≃ A y
   e y = (f y , i y)

   d : singleton-type' x ≃ Σ A
   d = Σ-cong e

   γ : is-singleton (Σ A)
   γ = equiv-to-singleton (≃-sym d) (singleton-types'-are-singletons X x)


singleton-equiv-lemma : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (x : X)
                      → (f : (y : X) → x ≡ y → A y)
                      → is-singleton (Σ A)
                      → (y : X) → is-equiv (f y)

singleton-equiv-lemma {𝓤} {𝓥} {X} {A} x f i = γ
 where
  abstract
   g : singleton-type' x → Σ A
   g = NatΣ f

   e : is-equiv g
   e = maps-of-singletons-are-equivs g (singleton-types'-are-singletons X x) i

   γ : (y : X) → is-equiv (f y)
   γ = NatΣ-equiv-gives-fiberwise-equiv f e
\end{code}

With this we can characterize univalence as follows:

\begin{code}
univalence⇒ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-singleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)

univalence⇒ ua X = equiv-singleton-lemma X (Id→Eq X) (ua X)


⇒univalence : ((X : 𝓤 ̇ ) → is-singleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y))
            → is-univalent 𝓤

⇒univalence i X = singleton-equiv-lemma X (Id→Eq X) (i X)
\end{code}

We can replace singleton by subsingleton and still have a logical
equivalence, and we sometimes need the characterization in this form:

\begin{code}
univalence→ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)

univalence→ ua X = singletons-are-subsingletons
                    (Σ (X ≃_)) (univalence⇒ ua X)


→univalence : ((X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y))
            → is-univalent 𝓤

→univalence i = ⇒univalence (λ X → pointed-subsingletons-are-singletons
                                    (Σ (X ≃_)) (X , id-≃ X) (i X))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="equivalenceinduction"></a> Equivalence induction

Under univalence, we get induction principles for type equivalences,
corresponding to the induction principles [`H`](HoTT-UF-Agda.html#H)
and [`J`](HoTT-UF-Agda.html#J) for identifications.  To prove a
property of equivalences, it is enough to prove it for the identity
equivalence `id-≃ X` for all `X`. In order to also easily derive an
equation for this, we perform the construction using the fact that
univalence implies that `Σ \(Y : 𝓤 ̇ ) → X ≃ Y` is a subsingleton for
any `X`.

\begin{code}
G-≃ : is-univalent 𝓤
    → (X : 𝓤 ̇ ) (A : (Σ \(Y : 𝓤 ̇ ) → X ≃ Y) → 𝓥 ̇ )
    → A (X , id-≃ X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A (Y , e)

G-≃ {𝓤} ua X A a Y e = transport A p a
 where
  t : Σ \(Y : 𝓤 ̇ ) → X ≃ Y
  t = (X , id-≃ X)

  p : t ≡ (Y , e)
  p = univalence→ {𝓤} ua X t (Y , e)


G-≃-equation : (ua : is-univalent 𝓤)
             → (X : 𝓤 ̇ ) (A : (Σ \(Y : 𝓤 ̇ ) → X ≃ Y) → 𝓥 ̇ )
             → (a : A (X  , id-≃ X))
             → G-≃ ua X A a X (id-≃ X) ≡ a

G-≃-equation {𝓤} {𝓥} ua X A a =

  G-≃ ua X A a X (id-≃ X) ≡⟨ refl _                       ⟩
  transport A p a         ≡⟨ ap (λ - → transport A - a) q ⟩
  transport A (refl t) a  ≡⟨ refl _                       ⟩
  a                       ∎

 where
  t : Σ \(Y : 𝓤 ̇ ) → X ≃ Y
  t = (X  , id-≃ X)

  p : t ≡ t
  p = univalence→ {𝓤} ua X t t

  q : p ≡ refl t
  q = subsingletons-are-sets (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)
       (univalence→ {𝓤} ua X) t t p (refl t)

H-≃ : is-univalent 𝓤
    → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → A X (id-≃ X) → (Y : 𝓤 ̇ ) (e : X ≃ Y) → A Y e

H-≃ ua X A = G-≃ ua X (Σ-induction A)


H-≃-equation : (ua : is-univalent 𝓤)
             → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
             → (a : A X  (id-≃ X))
             → H-≃ ua X A a X (id-≃ X) ≡ a

H-≃-equation ua X A = G-≃-equation ua X (Σ-induction A)
\end{code}

The induction principle `H-≃` keeps `X` fixed and lets `Y` vary, while
the induction principle `J-≃` lets both vary:

\begin{code}
J-≃ : is-univalent 𝓤
    → (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → ((X : 𝓤 ̇ ) → A X X (id-≃ X))
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

  b : B X (id-≃ X)
  b = λ (_ : is-equiv (𝑖𝑑 X)) → a

  γ : (e : X ≃ Y) → B Y e
  γ = H-≃ ua X B b Y
\end{code}

The above and the following say that to prove that a property of
*functions* holds for all equivalences, it is enough to prove it for all
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

For example, using `H-equiv` we see that for any pair of functions

   > `F : 𝓤 ̇ → 𝓤 ̇ `,

   > `𝓕 : {X Y : 𝓤 ̇ } → (X → Y) → F X → F Y`,

if `𝓕` preserves identities then it automatically preserves
composition of equivalences. More generally, it is enough that only
one of the factors is an equivalence:

\begin{code}
automatic-equiv-functoriality :

      {𝓤 : Universe}
      (F : 𝓤 ̇ → 𝓤 ̇ )
      (𝓕 : {X Y : 𝓤 ̇ }  → (X → Y) → F X → F Y)
      (𝓕-id : {X : 𝓤 ̇ } → 𝓕 (𝑖𝑑 X) ≡ 𝑖𝑑 (F X))
      {X Y Z : 𝓤 ̇ }
      (f : X → Y)
      (g : Y → Z)

    → is-univalent 𝓤 → is-equiv f + is-equiv g → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f

automatic-equiv-functoriality {𝓤} F 𝓕 𝓕-id {X} {Y} {Z} f g ua = γ
  where
   γ :  is-equiv f + is-equiv g → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f
   γ (inl i) = H-equiv ua X A a Y f i g
    where
     A : (Y : 𝓤 ̇ ) → (X → Y) → 𝓤 ̇
     A Y f = (g : Y → Z) → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f

     a : (g : X → Z) → 𝓕 g ≡ 𝓕 g ∘ 𝓕 id
     a g = ap (𝓕 g ∘_) (𝓕-id ⁻¹)

   γ (inr j) = H-equiv ua Y B b Z g j f
    where
     B : (Z : 𝓤 ̇ ) → (Y → Z) → 𝓤 ̇
     B Z g = (f : X → Y) → 𝓕 (g ∘ f) ≡ 𝓕 g ∘ 𝓕 f

     b : (f : X → Y) → 𝓕 f ≡ 𝓕 (𝑖𝑑 Y) ∘ 𝓕 f
     b f = ap (_∘ 𝓕 f) (𝓕-id ⁻¹)
\end{code}

Here is another example (see
[this](https://en.wikipedia.org/wiki/Change_of_variables) for the
terminology):

\begin{code}
Σ-change-of-variable' : is-univalent 𝓤
                      → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (f : X → Y)
                      → (i : is-equiv f)
                      → (Σ \(x : X) → A x) ≡ (Σ \(y : Y) → A (inverse f i y))

Σ-change-of-variable' {𝓤} {𝓥} ua {X} {Y} A f i = H-≃ ua X B b Y (f , i)
 where
   B : (Y : 𝓤 ̇ ) → X ≃ Y →  (𝓤 ⊔ 𝓥)⁺ ̇
   B Y (f , i) = (Σ A) ≡ (Σ (A ∘ inverse f i))

   b : B X (id-≃ X)
   b = refl (Σ A)
\end{code}

An unprimed version of this is given
[below](HoTT-UF-Agda.html#Σ-change-of-variable), after we study half
adjoint equivalences.

The above version using the inverse of `f` can be proved directly by
induction, but the following version is perhaps more natural.

\begin{code}
Σ-change-of-variable'' : is-univalent 𝓤
                       → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : Y → 𝓥 ̇ ) (f : X → Y)
                       → is-equiv f
                       → (Σ \(y : Y) → A y) ≡ (Σ \(x : X) → A (f x))

Σ-change-of-variable'' ua A f i = Σ-change-of-variable' ua A
                                  (inverse f i)
                                  (inverse-is-equiv f i)
\end{code}

This particular proof works only because inversion [is involutive on
the nose](HoTT-UF-Agda.html#inversion-involutive).

As another example we have the following:
\begin{code}
transport-map-along-≡ : {X Y Z : 𝓤 ̇ } (p : X ≡ Y) (g : X → Z)
                      → transport (λ - → - → Z) p g
                      ≡ g ∘ Id→fun (p ⁻¹)

transport-map-along-≡ (refl X) = refl


transport-map-along-≃ : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ }
                        (e : X ≃ Y) (g : X → Z)
                      → transport (λ - → - → Z) (Eq→Id ua X Y e) g
                      ≡ g ∘ Eq→fun (≃-sym e)

transport-map-along-≃ {𝓤} ua {X} {Y} {Z} = J-≃ ua A a X Y
 where
  A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓤 ̇
  A X Y e = (g : X → Z) → transport (λ - → - → Z) (Eq→Id ua X Y e) g
                        ≡ g ∘ Eq→fun (≃-sym e)
  a : (X : 𝓤 ̇ ) → A X X (id-≃ X)
  a X g = transport (λ - → - → Z) (Eq→Id ua X X (id-≃ X)) g ≡⟨ q      ⟩
          transport (λ - → - → Z) (refl X) g                ≡⟨ refl _ ⟩
          g                                                 ∎
    where
     p : Eq→Id ua X X (id-≃ X) ≡ refl X
     p = inverse-is-retraction (Id→Eq X X) (ua X X) (refl X)

     q = ap (λ - → transport (λ - → - → Z) - g ) p
\end{code}

An annoying feature of the use of `J` (rather than pattern matching on
`refl`) or `J-≃` is that we have to repeat what we want to prove, as
in the above examples.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="haes"></a> Half adjoint equivalences

An often useful alternative formulation of the notion of equivalence
is that of half adjoint equivalence. If we have a function

   > `f : X → Y`

with inversion data

   > `g : Y → X` ,

   > `η : g ∘ f ∼ id`,

   > `ε : f ∘ g ∼ id`,

then for any `x : X` we have that

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

ua-equivs-are-haes : is-univalent 𝓤
                   → {X Y : 𝓤 ̇ } (f : X → Y)
                   → is-equiv f → is-hae f

ua-equivs-are-haes ua {X} {Y} = J-equiv ua (λ X Y f → is-hae f) id-is-hae X Y


ua-invertibles-are-haes : is-univalent 𝓤
                        → {X Y : 𝓤 ̇ } (f : X → Y)
                        → invertible f → is-hae f

ua-invertibles-are-haes ua f i = ua-equivs-are-haes ua f (invertibles-are-equivs f i)
\end{code}

The above can be proved without univalence as follows, with a more
complicated argument coming from [category
theory](https://ncatlab.org/nlab/show/adjoint+equivalence). This
argument also allows us to have `X` and `Y` in different universes (an
example of an equivalence of types in different universes is
`Id→Eq`, as stated by univalence).

We first need some naturality lemmas:

\begin{code}
~-naturality : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
               (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
             → H x ∙ ap g p ≡ ap f p ∙ H y

~-naturality f g H {x} {_} {refl a} = refl-left ⁻¹


~-naturality' : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                (f g : X → A) (H : f ∼ g) {x y : X} {p : x ≡ y}
              → H x ∙ ap g p ∙ (H y)⁻¹ ≡ ap f p

~-naturality' f g H {x} {x} {refl x} = ⁻¹-right∙ (H x)


~-id-naturality : {X : 𝓤 ̇ }
                  (h : X → X) (η : h ∼ id) {x : X}
                → η (h x) ≡ ap h (η x)

~-id-naturality h η {x} =

   η (h x)                         ≡⟨ refl _ ⟩
   η (h x) ∙ refl (h x)            ≡⟨ i      ⟩
   η (h x) ∙ (η x ∙ (η x)⁻¹)       ≡⟨ ii     ⟩
   η (h x) ∙ η x ∙ (η x)⁻¹         ≡⟨ iii    ⟩
   η (h x) ∙ ap id (η x) ∙ (η x)⁻¹ ≡⟨ iv     ⟩
   ap h (η x)                      ∎

 where
  i   = ap (λ - → η(h x) ∙ -) ((⁻¹-right∙ (η x))⁻¹)
  ii  = (∙assoc (η (h x)) (η x) (η x ⁻¹))⁻¹
  iii = ap (λ - → η (h x) ∙ - ∙ η x ⁻¹) ((ap-id (η x))⁻¹)
  iv  = ~-naturality' h id η {h x} {x} {η x}
\end{code}

The idea of the following proof is to improve `ε` to be able to give
the required `τ`:

\begin{code}
invertibles-are-haes : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → invertible f → is-hae f

invertibles-are-haes f (g , η , ε) = g , η , ε' , τ
 where
  ε' = λ y → f (g y)         ≡⟨ (ε (f (g y)))⁻¹ ⟩
             f (g (f (g y))) ≡⟨ ap f (η (g y)) ⟩
             f (g y)         ≡⟨ ε y ⟩
             y               ∎

  module _ (x : domain f) where

   p = η (g (f x))       ≡⟨ ~-id-naturality (g ∘ f) η  ⟩
       ap (g ∘ f) (η x)  ≡⟨ ap-∘ f g (η x)             ⟩
       ap g (ap f (η x)) ∎

   q = ap f (η (g (f x))) ∙ ε (f x)         ≡⟨ i   ⟩
       ap f (ap g (ap f (η x))) ∙ ε (f x)   ≡⟨ ii  ⟩
       ap (f ∘ g) (ap f (η x)) ∙ ε (f x)    ≡⟨ iii ⟩
       ε (f (g (f x))) ∙ ap id (ap f (η x)) ≡⟨ iv  ⟩
       ε (f (g (f x))) ∙ ap f (η x)         ∎
    where
     i   = ap (λ - → - ∙ ε (f x)) (ap (ap f) p)
     ii  = ap (λ - → - ∙ ε (f x)) ((ap-∘ g f (ap f (η x)))⁻¹)
     iii = (~-naturality (f ∘ g) id ε {f (g (f x))} {f x} {ap f (η x)})⁻¹
     iv  = ap (λ - → ε (f (g (f x))) ∙ -) ((ap-∘ f id (η x))⁻¹)

   τ = ap f (η x)                                           ≡⟨ refl-left ⁻¹ ⟩
       refl (f (g (f x))) ∙ ap f (η x)                      ≡⟨ i            ⟩
       (ε (f (g (f x))))⁻¹ ∙ ε (f (g (f x))) ∙ ap f (η x)   ≡⟨ ii           ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ iii          ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl _       ⟩
       ε' (f x)                                             ∎
    where
     i   = ap (λ - → - ∙ ap f (η x)) ((⁻¹-left∙ (ε (f (g (f x)))))⁻¹)
     ii  = ∙assoc ((ε (f (g (f x))))⁻¹) (ε (f (g (f x)))) (ap f (η x))
     iii = ap (λ - → (ε (f (g (f x))))⁻¹ ∙ -) (q ⁻¹)


equivs-are-haes : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-equiv f → is-hae f

equivs-are-haes f i = invertibles-are-haes f (equivs-are-invertible f i)
\end{code}

Here is a use of the half adjoint condition, where, compared to
[`Σ-change-of-variable'`](HoTT-UF-Agda.html#Σ-change-of-variable), we
remove univalence from the hypothesis, generalize the universe of the
type `Y`, and weaken equality to equivalence in the conclusion. Notice
that the proof starts as that of
[`Σ-reindexing-retract`](HoTT-UF-Agda.html#Σ-reindexing-retract).

\begin{code}
Σ-change-of-variable-hae : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                         → is-hae f → Σ A ≃ Σ (A ∘ f)

Σ-change-of-variable-hae A f (g , η , ε , τ) = γ
 where
  φ : Σ A → Σ (A ∘ f)
  φ (y , a) = (g y , transport A ((ε y)⁻¹) a)

  ψ : Σ (A ∘ f) → Σ A
  ψ (x , a) = (f x , a)

  ψφ : (z : Σ A) → ψ (φ z) ≡ z
  ψφ (y , a) = to-Σ-≡ (ε y , transport-is-retraction A (ε y) a)

  φψ : (t : Σ (A ∘ f)) → φ (ψ t) ≡ t
  φψ (x , a) = to-Σ-≡ (η x , q)
   where
    b : A (f (g (f x)))
    b = transport A ((ε (f x))⁻¹) a

    q = transport (A ∘ f) (η x)  b ≡⟨ transport-ap A f (η x) b              ⟩
        transport A (ap f (η x)) b ≡⟨ ap (λ - → transport A - b) (τ x)      ⟩
        transport A (ε (f x))    b ≡⟨ transport-is-retraction A (ε (f x)) a ⟩
        a                          ∎

  γ : Σ A ≃ Σ (A ∘ f)
  γ = invertibility-gives-≃ φ (ψ , ψφ , φψ)


Σ-change-of-variable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                     → is-equiv f → Σ A ≃ Σ (A ∘ f)

Σ-change-of-variable A f i = Σ-change-of-variable-hae A f (equivs-are-haes f i)
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

*Exercise*. Assuming `funext`, prove that if a function `f : X → Y` is
an equivalence then so is the precomposition map `(-) ∘ f : (Y → Z) →
(X → Z)`.

The crucial step in [Voevodsky's
proof](https://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf)
that univalence implies `funext` is to establish the conclusion of the
above exercise assuming univalence instead. We prove this by
[equivalence induction](HoTT-UF-Agda.html#equivalenceinduction) on
`f`, which means that we only need to consider the case when `f` is an
identity function, for which precomposition with `f` is itself an
identity function (of a function type), and hence an equivalence:

\begin{code}
precomp-is-equiv : is-univalent 𝓤
                 → (X Y : 𝓤 ̇ ) (f : X → Y)
                 → is-equiv f
                 → (Z : 𝓤 ̇ ) → is-equiv (λ (g : Y → Z) → g ∘ f)

precomp-is-equiv {𝓤} ua =
   J-equiv ua
     (λ X Y (f : X → Y) → (Z : 𝓤 ̇ ) → is-equiv (λ g → g ∘ f))
     (λ X Z → id-is-equiv (X → Z))
\end{code}

With this we can prove the desired result as follows.

\begin{code}
univalence-gives-funext : is-univalent 𝓤 → funext 𝓥 𝓤
univalence-gives-funext {𝓤} {𝓥} ua {X} {Y} {f₀} {f₁} = γ
 where
  Δ : 𝓤 ̇
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
  φ-is-equiv = precomp-is-equiv ua Y Δ δ δ-is-equiv Y

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
  γ' h = f₀                             ≡⟨ refl _                               ⟩
         (λ x → f₀ x)                   ≡⟨ refl _                               ⟩
         (λ x → π₀ (f₀ x , f₁ x , h x)) ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) q ⟩
         (λ x → π₁ (f₀ x , f₁ x , h x)) ≡⟨ refl _                               ⟩
         (λ x → f₁ x)                   ≡⟨ refl _                               ⟩
         f₁                             ∎
\end{code}

So notice that this relies on the so-called η-rule for judgmental
equality of functions, namely

   > `f = λ x → f x`.

Without it, we would only get that

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

Voevodsky showed that all these notions of function extensionality are
logically equivalent to saying that products of singletons are
singletons:

\begin{code}
vvfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → is-singleton (A x))
             → is-singleton (Π A)

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
postcomp-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                    → funext 𝓦 𝓤 → funext 𝓦 𝓥
                    → (f : X → Y)
                    → invertible f
                    → invertible (λ (h : A → X) → f ∘ h)

postcomp-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = γ
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h

  g' : (A → Y) → (A → X)
  g' k = g ∘ k

  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)

  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

  γ : invertible f'
  γ = (g' , η' , ε')


postcomp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                  → funext 𝓦 𝓤 → funext 𝓦 𝓥
                  → (f : X → Y)
                  → is-equiv f
                  → is-equiv (λ (h : A → X) → f ∘ h)

postcomp-is-equiv fe fe' f e =
 invertibles-are-equivs
  (λ h → f ∘ h)
  (postcomp-invertible fe fe' f (equivs-are-invertible f e))


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
  f-is-equiv = pr₁-equiv φ

  g : (X → Σ A) → (X → X)
  g h = f ∘ h

  e : is-equiv g
  e = postcomp-is-equiv fe fe' f f-is-equiv

  i : is-singleton (Σ \(h : X → Σ A) → f ∘ h ≡ 𝑖𝑑 X)
  i = e (𝑖𝑑 X)

  r : (Σ \(h : X → Σ A) → f ∘ h ≡ 𝑖𝑑 X) → Π A
  r (h , p) x = transport A (happly (f ∘ h) (𝑖𝑑 X) p x) (pr₂ (h x))

  s : Π A → (Σ \(h : X → Σ A) → f ∘ h ≡ 𝑖𝑑 X)
  s φ = (λ x → x , φ x) , refl (𝑖𝑑 X)

  η : ∀ φ → r (s φ) ≡ φ
  η φ = refl (r (s φ))

  γ : is-singleton (Π A)
  γ = retract-of-singleton (r , s , η) i
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

The function `χ` gives the *characteristic function* of a map into `Y`:

\begin{code}
χ : (Y : 𝓤 ̇ ) → 𝓤 / Y  → (Y → 𝓤 ̇ )
χ Y (X , f) = fiber f
\end{code}

We say that a universe is a map classifier if the above function is an equivalence for every `Y` in the universe:

\begin{code}
is-map-classifier : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-map-classifier 𝓤 = (Y : 𝓤 ̇ ) → is-equiv (χ Y)
\end{code}

Any `Y → 𝓤` is the characteristic function of some map into `Y` by
taking its total space and the first projection:

\begin{code}
𝕋 : (Y : 𝓤 ̇ ) → (Y → 𝓤 ̇ ) → 𝓤 / Y
𝕋 Y A = Σ A , pr₁


χη : is-univalent 𝓤
   → (Y : 𝓤 ̇ ) → (σ : 𝓤 / Y) → 𝕋 Y (χ Y σ) ≡ σ

χη ua Y (X , f) = r
 where
  e : Σ (fiber f) ≃ X
  e = total-fiber-is-domain f

  p : Σ (fiber f) ≡ X
  p = Eq→Id ua (Σ (fiber f)) X e

  observation : Eq→fun (≃-sym e) ≡ (λ x → f x , x , refl (f x))
  observation = refl _

  q = transport (λ - → - → Y) p pr₁ ≡⟨ transport-map-along-≃ ua e pr₁ ⟩
      pr₁ ∘ Eq→fun (≃-sym e)        ≡⟨ refl _                         ⟩
      f                             ∎

  r : (Σ (fiber f) , pr₁) ≡ (X , f)
  r = to-Σ-≡ (p , q)


χε : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
   → (Y : 𝓤 ̇ ) (A : Y → 𝓤 ̇ ) → χ Y (𝕋 Y A) ≡ A

χε ua fe Y A = fe γ
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
  γ y = Eq→Id ua _ _ (invertibility-gives-≃ (f y) (g y , η y , ε y))


universes-are-map-classifiers : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                              → is-map-classifier 𝓤

universes-are-map-classifiers ua fe Y = invertibles-are-equivs (χ Y)
                                         (𝕋 Y , χη ua Y , χε ua fe Y)
\end{code}

Therefore we have the following canonical equivalence:

\begin{code}
map-classification : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                   → (Y : 𝓤 ̇ ) → 𝓤 / Y ≃ (Y → 𝓤 ̇ )

map-classification ua fe Y = χ Y , universes-are-map-classifiers ua fe Y
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


being-singleton-is-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ }
                                → is-subsingleton (is-singleton X)

being-singleton-is-subsingleton fe {X} (x , φ) (y , γ) = p
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)

  s : is-set X
  s = subsingletons-are-sets X i

  p : (x , φ) ≡ (y , γ)
  p = to-Σ-≡ (φ y , fe (λ (z : X) → s y z _ _))


being-equiv-is-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-subsingleton (is-equiv f)

being-equiv-is-subsingleton fe fe' f =
 Π-is-subsingleton fe
  (λ x → being-singleton-is-subsingleton fe')


univalence-is-subsingleton : is-univalent (𝓤 ⁺)
                           → is-subsingleton (is-univalent 𝓤)

univalence-is-subsingleton {𝓤} ua⁺ ua ua' = p
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
       (λ Y → being-equiv-is-subsingleton dfe₁ dfe₂ (Id→Eq X Y)))

  p : ua ≡ ua'
  p = i ua ua'
\end{code}

So if all universes are univalent then "being univalent" is a
subsingleton, and hence a singleton. This hypothesis of global
univalence cannot be expressed in our MLTT that only has `ω` many
universes, because global univalence would have to live in the first
universe after them. Agda [does
have](https://agda.readthedocs.io/en/latest/language/universe-levels.html#expressions-of-kind-set)
such a universe `𝓤ω,` and so we can formulate it here. There would be
no problem in extending our MLTT to have such a universe if we so
wished, in which case we would be able to formulate and prove:

\begin{code}
Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-subsingletonω : Univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-subsingletonω {𝓤} γ = univalence-is-subsingleton (γ (𝓤 ⁺))

univalence-is-a-singleton : Univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-singleton {𝓤} γ = pointed-subsingletons-are-singletons
                                   (is-univalent 𝓤)
                                   (γ 𝓤)
                                   (univalence-is-subsingletonω γ)
\end{code}

That the type `univalence` would be a subsingleton can't even be
formulated in the absence of a successor `𝓤ω⁺` of `𝓤ω`, and Agda
doesn't have such a successor universe (but there isn't any
fundamental reason why it couldn't have it).

In the absence of a universe `𝓤ω` in our MLTT, we can simply have an
[axiom schema](https://en.wikipedia.org/wiki/Axiom_schema), consisting
of `ω`-many axioms, stating that each universe is univalent. Then we
can prove in our MLTT that the univalence property for each inverse is
a (sub)singleton, with `ω`-many proofs (or just one schematic proof
with a free variable for a universe `𝓤ₙ`).

It follows immediately from the above that global univalence gives
global function extensionality.

\begin{code}
global-dfunext : 𝓤ω
global-dfunext = ∀ {𝓤 𝓥} → dfunext 𝓤 𝓥

univalence-gives-global-dfunext : Univalence → global-dfunext
univalence-gives-global-dfunext ua {𝓤} {𝓥} = univalence-gives-dfunext'
                                               (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

global-hfunext : 𝓤ω
global-hfunext = ∀ {𝓤 𝓥} → hfunext 𝓤 𝓥

univalence-gives-global-hfunext : Univalence → global-hfunext
univalence-gives-global-hfunext ua {𝓤} {𝓥} = univalence-gives-hfunext'
                                               (ua 𝓤) (ua (𝓤 ⊔ 𝓥))
\end{code}


#### `vvfunext 𝓤 𝓥` and `hfunext 𝓤 𝓥` are (sub)singletons

We need a version of
[`Π-is-subsingleton`](HoTT-UF-Agda.html#Π-is-subsingleton) for
dependent functions with implicit arguments.

\begin{code}
Π-is-subsingleton' : dfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                   → ((x : X) → is-subsingleton (A x))
                   → is-subsingleton ({x : X} → A x)

Π-is-subsingleton' fe {X} {A} i = γ
 where
  ρ : ({x : X} → A x) ◁ Π A
  ρ = (λ f {x} → f x) , (λ g x → g {x}) , refl

  γ : is-subsingleton ({x : X} → A x)
  γ = retract-of-subsingleton ρ (Π-is-subsingleton fe i)

\end{code}

To show that `vvfunext 𝓤 𝓥` and `hfunext 𝓤 𝓥` are subsingletons, we
need assumptions of function extensionality for higher universes:

\begin{code}
vv-and-hfunext-are-subsingletons-lemma  : dfunext (𝓤 ⁺)       (𝓤 ⊔ (𝓥 ⁺))
                                        → dfunext (𝓤 ⊔ (𝓥 ⁺)) (𝓤 ⊔ 𝓥)
                                        → dfunext (𝓤 ⊔ 𝓥)     (𝓤 ⊔ 𝓥)

                                        → is-subsingleton (vvfunext 𝓤 𝓥)
                                        × is-subsingleton (hfunext  𝓤 𝓥)

vv-and-hfunext-are-subsingletons-lemma {𝓤} {𝓥} dfe dfe' dfe'' = φ , γ
 where
  φ : is-subsingleton (vvfunext 𝓤 𝓥)
  φ = Π-is-subsingleton' dfe
       (λ X → Π-is-subsingleton' dfe'
       (λ A → Π-is-subsingleton dfe''
       (λ i → being-singleton-is-subsingleton dfe'')))

  γ : is-subsingleton (hfunext 𝓤 𝓥)
  γ = Π-is-subsingleton' dfe
       (λ X → Π-is-subsingleton' dfe'
       (λ A → Π-is-subsingleton dfe''
       (λ f → Π-is-subsingleton dfe''
       (λ g → being-equiv-is-subsingleton dfe'' dfe''
               (happly f g)))))
\end{code}

Hence they are singletons assuming global univalence (or just global
function extensionality, of any kind):

\begin{code}
vv-and-hfunext-are-singletons : Univalence
                              → is-singleton (vvfunext 𝓤 𝓥)
                              × is-singleton (hfunext  𝓤 𝓥)

vv-and-hfunext-are-singletons {𝓤} {𝓥} ua =

 f (vv-and-hfunext-are-subsingletons-lemma
     (univalence-gives-dfunext' (ua (𝓤 ⁺))       (ua ((𝓤 ⁺) ⊔ (𝓥 ⁺))))
     (univalence-gives-dfunext' (ua (𝓤 ⊔ (𝓥 ⁺))) (ua (𝓤 ⊔ (𝓥 ⁺))))
     (univalence-gives-dfunext' (ua (𝓤 ⊔ 𝓥))     (ua (𝓤 ⊔ 𝓥))))

 where
  f : is-subsingleton (vvfunext 𝓤 𝓥) × is-subsingleton (hfunext 𝓤 𝓥)
    → is-singleton (vvfunext 𝓤 𝓥) × is-singleton (hfunext 𝓤 𝓥)

  f (i , j) = pointed-subsingletons-are-singletons (vvfunext 𝓤 𝓥)
                (univalence-gives-vvfunext' (ua 𝓤) (ua (𝓤 ⊔ 𝓥))) i ,

              pointed-subsingletons-are-singletons (hfunext 𝓤 𝓥)
                (univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⊔ 𝓥))) j
\end{code}

However, `funext 𝓤 𝓤` and `dfunext 𝓤 𝓤` are not subsingletons (see the
HoTT book).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="unique-existence"></a> Unique existence in univalent mathematics

Unique existence of `x : X` with `A x` in univalent mathematics, written

   > `∃! \(x : X) → A x`

or simply

   > `∃! A`,

requires that not only the `x : X` but also the `a : A x` is
unique. More precisely, we require that there is a unique *pair* `(x ,
a) : Σ A`.

This is particularly important in the formulation of universal
properties involving types that are not necessarily sets, where it
generalizes the categorical notion of uniqueness up to unique
isomorphism.

\begin{code}
∃! : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
∃! A = is-singleton (Σ A)


unique-existence-is-subsingleton : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                                 → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                                 → is-subsingleton (∃! A)

unique-existence-is-subsingleton A fe = being-singleton-is-subsingleton fe


unique-existence-gives-weak-unique-existence : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) →

    (∃! \(x : X) → A x)
  → (Σ \(x : X) → A x) × ((x y : X) → A x → A y → x ≡ y)

unique-existence-gives-weak-unique-existence A s = center (Σ A) s , u
 where
  u : ∀ x y → A x → A y → x ≡ y
  u x y a b = ap pr₁ (singletons-are-subsingletons (Σ A) s (x , a) (y , b))
\end{code}

The converse holds if each `A x` is a subsingleton:

\begin{code}
weak-unique-existence-gives-unique-existence-sometimes : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) →

    ((x : X) → is-subsingleton (A x))

  → ((Σ \(x : X) → A x) × ((x y : X) → A x → A y → x ≡ y))
  → (∃! \(x : X) → A x)

weak-unique-existence-gives-unique-existence-sometimes A i ((x , a) , u) = (x , a) , φ
 where
  φ : (σ : Σ A) → x , a ≡ σ
  φ (y , b) = to-Σ-≡ (u x y a b , i y _ _)
\end{code}

*Exercise*. Find a counter-example in the absence of the requirement
 that all types `A x` are subsingletons.

Similarly, the existence of at most one `x : X` with `A x` should be
understood as

   > `is-subsingleton (Σ A)`,

but we will not introduce special notation for this concept, although
it will occur often.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="nnt"></a> Universal property of the natural numbers

The natural numbers have the [following universal
property](https://dl.acm.org/citation.cfm?id=3006383). What is
noteworthy here is that the type `Y` need not be a set, so that the
two equations can hold in multiple ways, but nevertheless we have
unique existence in the sense of the previous section. Moreover,
univalence is not needed.  Function extensionality suffices.

\begin{code}
ℕ-is-nno : hfunext 𝓤₀ 𝓤
         → (Y : 𝓤 ̇ ) (y₀ : Y) (g : Y → Y)
         → ∃! \(h : ℕ → Y) → (h 0 ≡ y₀) × (h ∘ succ ≡ g ∘ h)

ℕ-is-nno {𝓤} hfe Y y₀ g = γ
 where
\end{code}

We apply the same retraction techniques we used in order to prove that
[invertible maps are
equivalences](HoTT-UF-Agda.html#invertibles-are-equivs). We first show that, for any `h : ℕ → Y`, the type

   > `(h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h)`

is a retract of the type

   > `h ∼ ℕ-iteration Y y₀ g`

and hence, by function extensionality, we also have a retraction if we
replace pointwise equality `∼` by equality `≡`.  Thus the type

   > `Σ \(h : ℕ → Y) → (h 0 ≡ y₀) × (h ∘ succ ≡ g ∘ h)`

is a retract of the singleton type

   > `Σ \(h : ℕ → Y) → h ≡ ℕ-iteration Y y₀ g`,

and therefore is itself a singleton, as required.

Now we do this in Agda. We need both versions `hfunext` and `dfunext`
of function extensionality, where we have taken the first as an
assumption:

\begin{code}
  fe : dfunext 𝓤₀ 𝓤
  fe = hfunext-gives-dfunext hfe
\end{code}

We first establish the following retraction (which is automatically an
equivalence, but we don't need this fact).

\begin{code}
  lemma₀ : (h : ℕ → Y) → ((h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h)) ◁ (h ∼ ℕ-iteration Y y₀ g)
  lemma₀ h = r , s , η
   where
    s : (h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h) → h ∼ ℕ-iteration Y y₀ g
    s (p , K) 0 = p
    s (p , K) (succ n) = h (succ n)                  ≡⟨ K n                ⟩
                         g (h n)                     ≡⟨ ap g (s (p , K) n) ⟩
                         g (ℕ-iteration Y y₀ g n)    ≡⟨ refl _             ⟩
                         ℕ-iteration Y y₀ g (succ n) ∎
\end{code}

The above section `s` is defined by induction on natural numbers, but
the following retraction `r` is defined directly. Above and below, the
identifications `refl _` are included for the sake of clarity. This
adds some extra steps to the proof of the retraction property (some of
which could be silent, but we choose to make explicit by further uses
of `refl _`).

\begin{code}
    r : codomain s → domain s
    r H = H 0 , (λ n → h (succ n)                  ≡⟨ H (succ n)     ⟩
                       ℕ-iteration Y y₀ g (succ n) ≡⟨ refl _         ⟩
                       g (ℕ-iteration Y y₀ g n)    ≡⟨ ap g ((H n)⁻¹) ⟩
                       g (h n )                    ∎)

    remark : ∀ n H → pr₂ (r H) n ≡ H (succ n) ∙ (refl _ ∙ ap g ((H n)⁻¹))
    remark n H = refl _
\end{code}

The retraction property doesn't need induction on natural numbers:

\begin{code}
    η : (z : (h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h)) → r (s z) ≡ z
    η (p , K) = q
     where
      v = λ n →
       s (p , K) (succ n) ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹))                  ≡⟨ refl _ ⟩
       K n ∙  ap g (s (p , K) n) ∙  refl _ ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹)) ≡⟨ refl _ ⟩
       K n ∙  ap g (s (p , K) n) ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹))           ≡⟨ i   n  ⟩
       K n ∙  ap g (s (p , K) n) ∙  ap g ((s (p , K) n) ⁻¹)                    ≡⟨ ii  n  ⟩
       K n ∙ (ap g (s (p , K) n) ∙  ap g ((s (p , K) n) ⁻¹))                   ≡⟨ iii n  ⟩
       K n ∙ (ap g (s (p , K) n) ∙ (ap g  (s (p , K) n))⁻¹)                    ≡⟨ iv  n  ⟩
       K n ∙ refl _                                                            ≡⟨ refl _ ⟩
       K n                                                                     ∎
        where
         i   = λ n → ap (λ - → K n ∙ ap g (s (p , K) n) ∙ -)
                        (refl-left {_} {_} {_} {_} {ap g ((s (p , K) n)⁻¹)})
         ii  = λ n → ∙assoc (K n) (ap g (s (p , K) n)) (ap g ((s (p , K) n)⁻¹))
         iii = λ n → ap (λ - → K n ∙ (ap g (s (p , K) n) ∙ -)) (ap⁻¹ g (s (p , K) n) ⁻¹)
         iv  = λ n → ap (K n ∙_) (⁻¹-right∙ (ap g (s (p , K) n)))

      q = r (s (p , K))                                                      ≡⟨ refl _ ⟩
          p , (λ n → s (p , K) (succ n) ∙ (refl _ ∙ ap g ((s (p , K) n)⁻¹))) ≡⟨ vi     ⟩
          p , K                                                              ∎
       where
        vi = ap (p ,_) (fe v)


  lemma₁ = λ h → (h 0 ≡ y₀) × (h ∘ succ ≡ g ∘ h) ◁⟨ i h      ⟩
                 (h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h) ◁⟨ lemma₀ h ⟩
                 (h ∼ ℕ-iteration Y y₀ g)        ◁⟨ ii h     ⟩
                 (h ≡ ℕ-iteration Y y₀ g)        ◀
   where
    i  = λ h → Σ-retract (λ _ → ≃-gives-◁ (happly (h ∘ succ) (g ∘ h) , hfe _ _))
    ii = λ h → ≃-gives-▷ (happly h (ℕ-iteration Y y₀ g) , hfe _ _)

  lemma₂ : (Σ \(h : ℕ → Y) → (h 0 ≡ y₀) × (h ∘ succ ≡ g ∘ h))
         ◁ (Σ \(h : ℕ → Y) → h ≡ ℕ-iteration Y y₀ g)

  lemma₂ = Σ-retract lemma₁

  γ : is-singleton (Σ \(h : ℕ → Y) → (h 0 ≡ y₀) × (h ∘ succ ≡ g ∘ h))
  γ = retract-of-singleton lemma₂
                           (singleton-types-are-singletons (ℕ → Y) (ℕ-iteration Y y₀ g))
\end{code}

This concludes the proof of `ℕ-is-nno`. We say that `ℕ` is a [natural
numbers object](https://en.wikipedia.org/wiki/Natural_number_object),
or, more precisely, the triple `(ℕ , 0 , succ)` is a natural numbers
object.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="morefunextuses"></a> More consequences of function extensionality

\begin{code}
being-subsingleton-is-subsingleton : {X : 𝓤 ̇ } → dfunext 𝓤 𝓤
                                   → is-subsingleton (is-subsingleton X)

being-subsingleton-is-subsingleton {𝓤} {X} fe i j = c
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

Here the version `hfunext` of function extensionality is what is
needed:

\begin{code}
Π-is-set : hfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set (A x)) → is-set (Π A)

Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = hfunext-gives-dfunext hfe ((λ x → s x (f x) (g x) (p x) (q x)))

  b : is-subsingleton (f ≡ g)
  b = equiv-to-subsingleton (happly f g , hfe f g) a


being-set-is-subsingleton : dfunext 𝓤 𝓤
                          → {X : 𝓤 ̇ } → is-subsingleton (is-set X)

being-set-is-subsingleton fe =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
  (λ y → being-subsingleton-is-subsingleton fe))
\end{code}

More generally:

\begin{code}
hlevel-relation-is-subsingleton : dfunext 𝓤 𝓤
                                → (n : ℕ) (X : 𝓤 ̇ )
                                → is-subsingleton (X is-of-hlevel n)

hlevel-relation-is-subsingleton {𝓤} fe zero X =
 being-singleton-is-subsingleton fe

hlevel-relation-is-subsingleton fe (succ n) X =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
  (λ x' → hlevel-relation-is-subsingleton fe n (x ≡ x')))
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
  q = being-equiv-is-subsingleton fe fe' (h ∘ g ∘ f) _ _


≃-sym-involutive : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) →
                   {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                 → ≃-sym (≃-sym α) ≡ α

≃-sym-involutive fe fe' (f , a) = to-Σ-≡
                                   (inversion-involutive f a ,
                                    being-equiv-is-subsingleton fe fe' f _ _)

≃-sym-is-equiv : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-equiv (≃-sym {𝓤} {𝓥} {X} {Y})

≃-sym-is-equiv fe₀ fe₁ fe₂ = invertibles-are-equivs ≃-sym
                                (≃-sym ,
                                 ≃-sym-involutive fe₀ fe₂ ,
                                 ≃-sym-involutive fe₁ fe₂)
\end{code}

*Exercise*. The hlevels are closed under `Σ` and, using `hfunext`, also
under `Π`. Univalence is not needed, but makes the proof easier.  (Without
univalence, we need to show that the hlevels are
closed under equivalence first.)

\begin{code}
Π-cong : dfunext 𝓤 𝓥 → dfunext 𝓤 𝓦
       → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Y' : X → 𝓦 ̇ }
       → ((x : X) → Y x ≃ Y' x) → Π Y ≃ Π Y'

Π-cong fe fe' {X} {Y} {Y'} φ = invertibility-gives-≃ F (G , GF , FG)
 where
  f : (x : X) → Y x → Y' x
  f x = Eq→fun (φ x)

  e : (x : X) → is-equiv (f x)
  e x = Eq→fun-is-equiv (φ x)

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

  FG : (γ : ((x : X) → Y' x)) → F(G γ) ≡ γ
  FG γ = fe' (λ x → fg x (γ x))

  GF : (φ : ((x : X) → Y x)) → G(F φ) ≡ φ
  GF φ = fe (λ x → gf x (φ x))
\end{code}

An application of `Π-cong` is `hfunext₂-≃`:

\begin{code}
hfunext-≃ : hfunext 𝓤 𝓥
          → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A)
          → (f ≡ g) ≃ (f ∼ g)

hfunext-≃ hfe f g = (happly f g , hfe f g)

hfunext₂-≃ : hfunext 𝓤 (𝓥 ⊔ 𝓦) → hfunext 𝓥 𝓦
           → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : (x : X) → Y x → 𝓦 ̇ }
             (f g : (x : X) (y : Y x) → A x y)
           → (f ≡ g) ≃ (∀ x y → f x y ≡ g x y)

hfunext₂-≃ fe fe' {X} f g =

 (f ≡ g)                  ≃⟨ i  ⟩
 (∀ x → f x ≡ g x)        ≃⟨ ii ⟩
 (∀ x y → f x y ≡ g x y)  ■

 where
  i  = hfunext-≃ fe f g
  ii = Π-cong
        (hfunext-gives-dfunext fe)
        (hfunext-gives-dfunext fe)
        (λ x → hfunext-≃ fe' (f x) (g x))


precomp-invertible : dfunext 𝓥 𝓦 → dfunext 𝓤 𝓦
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y)
                   → invertible f
                   → invertible (λ (h : Y → Z) → h ∘ f)

precomp-invertible fe fe' {X} {Y} {Z} f (g , η , ε) = (g' , η' , ε')
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
it has a retraction. We now show that this notion is a subsingleton.
For that purpose, we first show that if a function has a retraction
then it has at most one section, and that if it has a section then it
has at most one retraction.

\begin{code}
at-most-one-section : dfunext 𝓥 𝓤 → hfunext 𝓥 𝓥
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → has-retraction f
                    → is-subsingleton (has-section f)

at-most-one-section {𝓥} {𝓤} fe hfe {X} {Y} f (g , gf) (h , fh) = d
 where
  fe' : dfunext 𝓥 𝓥
  fe' = hfunext-gives-dfunext hfe

  a : invertible f
  a = joyal-equivs-are-invertible f (((h , fh) , g , gf))

  b : is-singleton (fiber (λ h →  f ∘ h) id)
  b = invertibles-are-equivs (λ h → f ∘ h) (postcomp-invertible fe fe' f a) id

  r : fiber (λ h →  f ∘ h) id → has-section f
  r (h , p) = (h , happly (f ∘ h) id p)

  s : has-section f → fiber (λ h → f ∘ h) id
  s (h , η) = (h , fe' η)

  rs : (σ : has-section f) → r (s σ) ≡ σ
  rs (h , η) = to-Σ-≡' q
   where
    q : happly (f ∘ h) id (inverse (happly (f ∘ h) id) (hfe (f ∘ h) id) η) ≡ η
    q = inverse-is-section (happly (f ∘ h) id) (hfe (f ∘ h) id) η

  c : is-singleton (has-section f)
  c = retract-of-singleton (r , s , rs) b

  d : (σ : has-section f) → h , fh ≡ σ
  d = singletons-are-subsingletons (has-section f) c (h , fh)


at-most-one-retraction : hfunext 𝓤 𝓤 → dfunext 𝓥 𝓤
                       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → has-section f
                       → is-subsingleton (has-retraction f)

at-most-one-retraction {𝓤} {𝓥} hfe fe' {X} {Y} f (g , fg) (h , hf) = d
 where
  fe : dfunext 𝓤 𝓤
  fe = hfunext-gives-dfunext hfe

  a : invertible f
  a = joyal-equivs-are-invertible f ((g , fg) , (h , hf))

  b : is-singleton (fiber (λ h →  h ∘ f) id)
  b = invertibles-are-equivs (λ h → h ∘ f) (precomp-invertible fe' fe f a) id

  r : fiber (λ h →  h ∘ f) id → has-retraction f
  r (h , p) = (h , happly (h ∘ f) id p)

  s : has-retraction f → fiber (λ h →  h ∘ f) id
  s (h , η) = (h , fe η)

  rs : (σ : has-retraction f) → r (s σ) ≡ σ
  rs (h , η) = to-Σ-≡' q
   where
    q : happly (h ∘ f) id (inverse (happly (h ∘ f) id) (hfe (h ∘ f) id) η) ≡ η
    q = inverse-is-section (happly (h ∘ f) id) (hfe (h ∘ f) id) η

  c : is-singleton (has-retraction f)
  c = retract-of-singleton (r , s , rs) b

  d : (ρ : has-retraction f) → h , hf ≡ ρ
  d = singletons-are-subsingletons (has-retraction f) c (h , hf)


being-joyal-equiv-is-subsingleton : hfunext 𝓤 𝓤 → hfunext 𝓥 𝓥 → dfunext 𝓥 𝓤
                                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                  → (f : X → Y)
                                  → is-subsingleton (is-joyal-equiv f)

being-joyal-equiv-is-subsingleton fe₀ fe₁ fe₂ f =
 ×-is-subsingleton'
  (at-most-one-section fe₂ fe₁ f ,
   at-most-one-retraction fe₀ fe₂ f)
\end{code}

Another consequence of function extensionality is that emptiness is a
subsingleton:

\begin{code}
emptiness-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ )
                          → is-subsingleton (is-empty X)
emptiness-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))
\end{code}

If `P` is a subsingleton, then so is `P + ¬ P`. More
generally:

\begin{code}
+-is-subsingleton : {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
                  → is-subsingleton P
                  → is-subsingleton Q
                  → (P → Q → 𝟘) → is-subsingleton (P + Q)

+-is-subsingleton {𝓤} {𝓥} {P} {Q} i j f = γ
 where
  γ : (x y : P + Q) → x ≡ y
  γ (inl p) (inl p') = ap inl (i p p')
  γ (inl p) (inr q)  = !𝟘 (inl p ≡ inr q) (f p q)
  γ (inr q) (inl p)  = !𝟘 (inr q ≡ inl p) (f p q)
  γ (inr q) (inr q') = ap inr (j q q')

+-is-subsingleton' : dfunext 𝓤 𝓤₀
                   → {P : 𝓤 ̇ } → is-subsingleton P → is-subsingleton (P + ¬ P)

+-is-subsingleton' fe {P} i = +-is-subsingleton i
                               (emptiness-is-subsingleton fe P)
                               (λ p n → n p)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="propositionalextensionality"></a> Propositional extensionality and the powerset

We have been using the mathematical terminology "subsingleton", but
tradition in the formulation of the next notion demands the logical
terminology "proposition". Propositional extensionality says that any
two logically equivalent propositions are equal:

\begin{code}
propext : ∀ 𝓤  → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

global-propext : 𝓤ω
global-propext = ∀ {𝓤} → propext 𝓤
\end{code}

This is directly implied by univalence:

\begin{code}
univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g =
 Eq→Id ua P Q
  (logically-equivalent-subsingletons-are-equivalent P Q i j (f , g))
\end{code}

Under the additional hypothesis of function extensionality, the converse of the above holds. We need a lemma for that.

\begin{code}
Id-from-subsingleton : propext 𝓤 → dfunext 𝓤 𝓤
                     → (P : 𝓤 ̇ )
                     → is-subsingleton P
                     → (X : 𝓤 ̇ ) → is-subsingleton (P ≡ X)

Id-from-subsingleton {𝓤} pe fe P i = Hedberg P (λ X → h X , k X)
 where
  module _ (X : 𝓤 ̇ ) where
   f : P ≡ X → is-subsingleton X × (P ⇔ X)
   f p = transport is-subsingleton p i , Id→fun p , (Id→fun (p ⁻¹))

   g : is-subsingleton X × (P ⇔ X) → P ≡ X
   g (l , φ , ψ) = pe i l φ ψ

   h : P ≡ X → P ≡ X
   h = g ∘ f

   j : is-subsingleton (is-subsingleton X × (P ⇔ X))
   j = ×-is-subsingleton'
        ((λ (_ : P ⇔ X) → being-subsingleton-is-subsingleton fe) ,
         (λ (l : is-subsingleton X) → ×-is-subsingleton
                                       (Π-is-subsingleton fe (λ p → l))
                                       (Π-is-subsingleton fe (λ x → i))))

   k : wconstant h
   k p q = ap g (j (f p) (f q))


subsingleton-univalence : propext 𝓤 → dfunext 𝓤 𝓤
                        → (P : 𝓤 ̇ )
                        → is-subsingleton P
                        → (X : 𝓤 ̇ ) → is-equiv (Id→Eq P X)

subsingleton-univalence {𝓤} pe fe P i X = γ
 where
  l : P ≃ X → is-subsingleton X
  l e = equiv-to-subsingleton (≃-sym e) i

  eqtoid : P ≃ X → P ≡ X
  eqtoid e = pe i (equiv-to-subsingleton (≃-sym e) i)
                (Eq→fun e) (Eq→fun (≃-sym e))

  m : is-subsingleton (P ≃ X)
  m (f , k) (f' , k') = to-Σ-≡ (fe (λ x → j (f x) (f' x)) ,
                                being-equiv-is-subsingleton fe fe f' _ k')
    where
     j : is-subsingleton X
     j = equiv-to-subsingleton (≃-sym (f , k)) i

  ε : (e : P ≃ X) → Id→Eq P X (eqtoid e) ≡ e
  ε e = m (Id→Eq P X (eqtoid e)) e

  η : (q : P ≡ X) → eqtoid (Id→Eq P X q) ≡ q
  η q = Id-from-subsingleton pe fe P i X (eqtoid (Id→Eq P X q)) q

  γ : is-equiv (Id→Eq P X)
  γ = invertibles-are-equivs (Id→Eq P X) (eqtoid , η , ε)


subsingleton-univalence-≃ : propext 𝓤 → dfunext 𝓤 𝓤
                          → (X P : 𝓤 ̇ ) → is-subsingleton P → (P ≡ X) ≃ (P ≃ X)

subsingleton-univalence-≃ pe fe X P i = Id→Eq P X ,
                                        subsingleton-univalence pe fe P i X
\end{code}

We also need a version of propositional extensionality for the type
`Ω 𝓤` of subsingletons in a given universe `𝓤`,
which lives in the next universe:

\begin{code}
Ω : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω 𝓤 = Σ \(P : 𝓤 ̇ ) → is-subsingleton P

_holds : Ω 𝓤 → 𝓤 ̇
_holds (P , i) = P

holds-is-subsingleton : (p : Ω 𝓤) → is-subsingleton (p holds)
holds-is-subsingleton (P , i) = i


Ω-ext : dfunext 𝓤 𝓤 → propext 𝓤 → {p q : Ω 𝓤}
      → (p holds → q holds) → (q holds → p holds) → p ≡ q

Ω-ext {𝓤} fe pe {p} {q} f g =
 to-Σ-≡ (pe (holds-is-subsingleton p) (holds-is-subsingleton q) f g ,
         being-subsingleton-is-subsingleton fe _ _)
\end{code}

With this and Hedberg, we get that `Ω` is a set:

\begin{code}
Ω-is-a-set : dfunext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-a-set {𝓤} fe pe = types-with-wconstant-≡-endomaps-are-sets (Ω 𝓤) c
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)

  i : (p q : Ω 𝓤) → is-subsingleton (A p q)
  i p q = Σ-is-subsingleton
           (Π-is-subsingleton fe
             (λ _ → holds-is-subsingleton q))
             (λ _ → Π-is-subsingleton fe (λ _ → holds-is-subsingleton p))

  g : (p q : Ω 𝓤) → p ≡ q → A p q
  g p q e = (u , v)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    u : p holds → q holds
    u = Id→fun a
    v : q holds → p holds
    v = Id→fun (a ⁻¹)

  h : (p q : Ω 𝓤) → A p q → p ≡ q
  h p q (u , v) = Ω-ext fe pe u v

  f : (p q : Ω 𝓤) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)

  k : (p q : Ω 𝓤) (d e : p ≡ q) → f p q d ≡ f p q e
  k p q d e = ap (h p q) (i p q (g p q d) (g p q e))

  c : (p q : Ω 𝓤) → Σ \(f : p ≡ q → p ≡ q) → wconstant f
  c p q = (f p q , k p q)
\end{code}

Hence powersets, even of types that are not sets, are always sets.

\begin{code}
powersets-are-sets : hfunext 𝓤 (𝓥 ⁺) → dfunext 𝓥 𝓥 → propext 𝓥
                   → {X : 𝓤 ̇ } → is-set (X → Ω 𝓥)

powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-a-set fe' pe)
\end{code}

The above considers `X : 𝓤` and `Ω 𝓥`. When the two universes `𝓤` and
`𝓥` are the same, we adopt the usual notation `𝓟 X` for the powerset
`X → Ω 𝓤` of `X`.

\begin{code}
𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤
\end{code}

Notice also that both `Ω` and the powerset live in the next universe. With
[propositional resizing](HoTT-UF-Agda.html#resizing), we get
equivalent copies in the same universe.

Membership and containment for elements of the powerset are defined as follows:

\begin{code}
_∈_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓤 ̇
x ∈ A = A x holds

_⊆_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓤 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-is-subsingleton : {X : 𝓤 ̇ } (x : X) (A : 𝓟 X) → is-subsingleton (x ∈ A)
∈-is-subsingleton x A = holds-is-subsingleton (A x)


⊆-is-subsingleton : dfunext 𝓤 𝓤
                  → {X : 𝓤 ̇ } (A B : 𝓟 X) → is-subsingleton (A ⊆ B)

⊆-is-subsingleton fe A B = Π-is-subsingleton fe
                            (λ x → Π-is-subsingleton fe
                            (λ _ → ∈-is-subsingleton x B))


⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 X) → A ⊆ A
⊆-refl A x = 𝑖𝑑 (x ∈ A)


⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence {X} A A (refl A) = ⊆-refl A , ⊆-refl A
\end{code}

Although `𝓟 X` is a set even if `X` is not, the total space
`Σ \(x : X) → A x holds` of a member `A : 𝓟 X` of the powerset need not
be a set. For instance, if `A x holds = 𝟙` for all `x : X`, then the total space is
equivalent to `X`, which may not be a set.

Propositional and functional extensionality give the usual extensionality condition for the powerset:

\begin{code}
subset-extensionality : propext 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } (A B : 𝓟 X)
                      → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality pe fe fe' {X} A B h k = fe' φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-Σ-≡ (pe (holds-is-subsingleton (A x))
                   (holds-is-subsingleton (B x)) (h x) (k x) ,
                being-subsingleton-is-subsingleton fe
                   (holds-is-subsingleton _)
                   (holds-is-subsingleton _))
\end{code}

And hence so does univalence:

\begin{code}
subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } (A B : 𝓟 X)
                       → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-dfunext (ua 𝓤))
                                 (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
\end{code}

For set-level mathematics, function extensionality and propositional
extensionality are often the only consequences of univalence that are
needed. A noteworthy exception is the theorem that the type of
ordinals in a universe is an ordinal in the next universe, which
requires univalence for sets (see the HoTT book or
[this](https://www.cs.bham.ac.uk/~mhe/agda-new/OrdinalOfOrdinals.html)).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="equivconstructions"></a> Some constructions with types of equivalences

We first prove some
properties of equivalence symmetrization and composition:

\begin{code}
id-≃-left : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
          → id-≃ X ● α ≡ α

id-≃-left fe fe' α = to-Σ-≡
                        (refl _ ,
                         being-equiv-is-subsingleton fe fe' _ _ _)


≃-sym-left-inverse : dfunext 𝓥 𝓥
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                   → ≃-sym α ● α ≡ id-≃ Y

≃-sym-left-inverse fe (f , e) = to-Σ-≡
                                 (p ,
                                  being-equiv-is-subsingleton fe fe _ _ _)
 where
  p : f ∘ inverse f e ≡ id
  p = fe (inverse-is-section f e)


≃-sym-right-inverse : dfunext 𝓤 𝓤
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                    → α ● ≃-sym α ≡ id-≃ X

≃-sym-right-inverse fe (f , e) = to-Σ-≡
                                  (p ,
                                   being-equiv-is-subsingleton fe fe _ _ _)
 where
  p : inverse f e ∘ f ≡ id
  p = fe (inverse-is-retraction f e)
\end{code}

We then transfer the above to equivalence types:

\begin{code}
≃-Sym : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → (X ≃ Y) ≃ (Y ≃ X)

≃-Sym fe₀ fe₁ fe₂ = ≃-sym , ≃-sym-is-equiv fe₀ fe₁ fe₂


≃-Comp : dfunext 𝓦 (𝓥 ⊔ 𝓦) → dfunext (𝓥 ⊔ 𝓦) (𝓥 ⊔ 𝓦 )
       → dfunext 𝓥 𝓥 → dfunext 𝓦 (𝓤 ⊔ 𝓦)
       → dfunext (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓦 ) → dfunext 𝓤 𝓤
       → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ )
       → X ≃ Y → (Y ≃ Z) ≃ (X ≃ Z)

≃-Comp fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Z α = invertibility-gives-≃ (α ●_)
                                      ((≃-sym α ●_) , p , q)
 where
  p = λ β → ≃-sym α ● (α ● β) ≡⟨ ●-assoc fe₀ fe₁ (≃-sym α) α β        ⟩
            (≃-sym α ● α) ● β ≡⟨ ap (_● β) (≃-sym-left-inverse fe₂ α) ⟩
            id-≃ _ ● β        ≡⟨ id-≃-left fe₀ fe₁ _                  ⟩
            β                 ∎

  q = λ γ → α ● (≃-sym α ● γ) ≡⟨ ●-assoc fe₃ fe₄ α (≃-sym α) γ         ⟩
            (α ● ≃-sym α) ● γ ≡⟨ ap (_● γ) (≃-sym-right-inverse fe₅ α) ⟩
            id-≃ _ ● γ        ≡⟨ id-≃-left fe₃ fe₄ _                   ⟩
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

  X ≃ Y   ≃⟨ ≃-Comp fe₀ fe₁ fe₂ fe₃ fe₄ fe₅ Y (≃-sym α)  ⟩
  A ≃ Y   ≃⟨ ≃-Sym fe₃ fe₆ fe₄                           ⟩
  Y ≃ A   ≃⟨ ≃-Comp fe₆ fe₄ fe₇ fe₈ fe₉ fe₁₀ A (≃-sym β) ⟩
  B ≃ A   ≃⟨ ≃-Sym fe₈ fe₁₁ fe₉                          ⟩
  A ≃ B   ■
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
is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)


being-embedding-is-subsingleton : global-dfunext
                                → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-subsingleton (is-embedding f)

being-embedding-is-subsingleton fe f =
 Π-is-subsingleton fe
  (λ x → being-subsingleton-is-subsingleton fe)
\end{code}

For example, if `A` is a subsingleton, then the second projection `A ×
X → X` is an embedding:

\begin{code}
pr₂-embedding : (A : 𝓤 ̇ ) (X : 𝓥 ̇ )
              → is-subsingleton A
              → is-embedding (λ (z : A × X) → pr₂ z)

pr₂-embedding A X i x ((a , x) , refl x) ((b , x) , refl x) = p
 where
  p : ((a , x) , refl x) ≡ ((b , x) , refl x)
  p = ap (λ - → ((- , x) , refl x)) (i a b)
\end{code}

*Exercise*. Show that the converse of `pr₂-embedding` holds.

More generally, with the arguments swapped, the projection `Σ A → X`
is an embedding if `A x` is a subsingleton for every `x : X`:

\begin{code}
pr₁-embedding : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
              → ((x : X) → is-subsingleton (A x))
              → is-embedding (pr₁ {𝓤} {𝓥} {X} {A})

pr₁-embedding i x ((x , a) , refl x) ((x , a') , refl x) = γ
 where
  γ : (x , a) , refl x ≡ (x , a') , refl x
  γ = ap (λ - → (x , -) , refl x) (i x a a')
\end{code}

*Exercise*. Show that the converse of `pr₁-embedding` holds.

\begin{code}
equivs-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        (f : X → Y)
                      → is-equiv f → is-embedding f

equivs-are-embeddings f i y = singletons-are-subsingletons (fiber f y) (i y)


id-is-embedding : {X : 𝓤 ̇ } → is-embedding (𝑖𝑑 X)
id-is-embedding {𝓤} {X} = equivs-are-embeddings id (id-is-equiv X)


∘-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
              {f : X → Y} {g : Y → Z}
            → is-embedding g  → is-embedding f → is-embedding (g ∘ f)

∘-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} d e = h
 where
  A : (z : Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  A z = Σ \(w : fiber g z) → fiber f (pr₁ w)

  i : (z : Z) → is-subsingleton (A z)
  i z = Σ-is-subsingleton (d z) (λ w → e (pr₁ w))

  φ : (z : Z) → fiber (g ∘ f) z → A z
  φ z (x , p) = (f x , p) , x , refl (f x)

  γ : (z : Z) → A z → fiber (g ∘ f) z
  γ z ((_ , p) , x , refl _) = x , p

  η : (z : Z) (t : fiber (g ∘ f) z) → γ z (φ z t) ≡ t
  η _ (x , refl _) = refl (x , refl ((g ∘ f) x))

  h : (z : Z) → is-subsingleton (fiber (g ∘ f) z)
  h z = lc-maps-reflect-subsingletons (φ z) (sections-are-lc (φ z) (γ z , η z)) (i z)
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
  γ x = singleton-equiv-lemma x (λ x' → ap f {x} {x'})
         (pointed-subsingletons-are-singletons
           (Σ \(x' : X) → f x ≡ f x') (x , (refl (f x))) (s x))


embedding-criterion-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-embedding f
                             → ((x' x : X) → (f x' ≡ f x) ≃ (x' ≡ x))

embedding-criterion-converse f e x' x = ≃-sym
                                         (ap f {x'} {x} ,
                                          embedding-gives-ap-is-equiv f e x' x)
\end{code}

Hence embeddings of arbitrary types are left cancellable, but the
converse fails in general.

*Exercise*. Left cancellable maps into *sets* are always embeddings.

We now introduce notation for the type of embeddings.

\begin{code}
_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ \(f : X → Y) → is-embedding f
\end{code}

The following justifies the terminology *subsingleton*:

*Exercise*. [(1)](HoTT-UF-Agda.html#the-subsingletons-are-the-subtypes-of-a-singleton)
 Show that `is-subsingleton X ⇔ (X ↪
 𝟙)`. [(2)](HoTT-UF-Agda.html#the-subsingletons-are-the-subtypes-of-a-singleton)
 Hence assuming function extensionality and propositional
 extensionality, conclude that `is-subsingleton X ≡ (X ↪ 𝟙)`.

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

By our definition of [`Nat`](HoTT-UF-Agda.html#Nat), for any
`A : X → 𝓥 ̇ ` and `x : X` we have

   > `Nat (𝓨 x) A = (y : X) → x ≡ y → A y`,

and, by [`Nats-are-natural`](HoTT-UF-Agda.html#Nats-are-natural), we
have that `Nat (𝓨 x) A` is the type of natural transformations from
the presheaf `𝓨 x` to the presheaf `A`.  The starting point of the
Yoneda Lemma, in our context, is that every such natural
transformation is a transport.

\begin{code}
transport-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                → (τ : Nat (𝓨 x) A)
                → (y : X) (p : x ≡ y) → τ y p ≡ transport A p (τ x (refl x))

transport-lemma A x τ x (refl x) = refl (τ x (refl x))
\end{code}

We denote the point `τ x (refl x)` in the above lemma by `𝓔 A x τ` as
refer to it as the *Yoneda element* of the transformation `τ`.

\begin{code}
𝓔 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → Nat (𝓨 x) A → A x
𝓔 A x τ = τ x (refl x)
\end{code}

The function

   > `𝓔 A x : Nat (𝓨 x) A → A x`

is an equivalence with
inverse

   > `𝓝 A x : A x → Nat (𝓨 x) A`,

the transport natural transformation induced by `A` and `x`:

\begin{code}
𝓝 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → A x → Nat (𝓨 x) A
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
is-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
is-fiberwise-equiv τ = ∀ x → is-equiv (τ x)


𝓔-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
           → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
           → is-fiberwise-equiv (𝓔 A)

𝓔-is-equiv fe fe' A x = invertibles-are-equivs (𝓔 A x )
                         (𝓝 A x , yoneda-η fe fe' A x , yoneda-ε A x)


𝓝-is-equiv : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
           → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
           → is-fiberwise-equiv (𝓝 A)

𝓝-is-equiv fe fe' A x = invertibles-are-equivs (𝓝 A x)
                         (𝓔 A x , yoneda-ε A x , yoneda-η fe fe' A x)
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
presheaf](https://en.wikipedia.org/wiki/Representable_functor#Universal_elements)
`A` corresponds in our context to an element of the type `is-singleton
(Σ A)`, which can also be written `∃! A`.

If the transport transformation is a fiberwise equivalence,
then `A` has a universal element. More generally, we have the following:

\begin{code}
retract-universal-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                        → ((y : X) → A y ◁ (x ≡ y))
                        → ∃! A

retract-universal-lemma A x ρ = i
 where
  σ : Σ A ◁ singleton-type' x
  σ = Σ-retract ρ

  i : ∃! A
  i = retract-of-singleton σ (singleton-types'-are-singletons (domain A) x)


fiberwise-equiv-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) (a : A x)
                          → is-fiberwise-equiv (𝓝 A x a)
                          → ∃! A
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
                        → ∃! A

representable-universal A (x , e) = retract-universal-lemma A x
                                     (λ x → ≃-gives-▷ (e x))


universal-fiberwise-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                          → ∃! A
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
                        → ∃! A
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

  i : ∃! A
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

To prove that [`𝓨 {𝓤} {X}` is an
embedding](https://arxiv.org/abs/1903.01211) of `X` into `X → 𝓤` for
any type `X : 𝓤`, we need the following two lemmas, which are
interesting in their own right:

\begin{code}
being-fiberwise-equiv-is-subsingleton : global-dfunext
                                      → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                      → (τ : Nat A B)
                                      → is-subsingleton (is-fiberwise-equiv τ)

being-fiberwise-equiv-is-subsingleton fe τ =
 Π-is-subsingleton fe
  (λ y → being-equiv-is-subsingleton fe fe (τ y))


being-representable-is-subsingleton : global-dfunext
                                    → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                                    → is-subsingleton (is-representable A)

being-representable-is-subsingleton fe {X} A r₀ r₁ = γ
 where
  u : ∃! A
  u = representable-universal A r₀

  i : (x : X) (τ : Nat (𝓨 x) A) → is-singleton (is-fiberwise-equiv τ)
  i x τ = pointed-subsingletons-are-singletons
           (is-fiberwise-equiv τ)
           (universal-fiberwise-equiv A x u τ)
           (being-fiberwise-equiv-is-subsingleton fe τ)

  ε : (x : X) → (𝓨 x ≃̇ A) ≃ A x
  ε x = ((y : X) → 𝓨 x y ≃ A y)                       ≃⟨ ΠΣ-distr-≃             ⟩
        (Σ \(τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ) ≃⟨ pr₁-≃ (i x)            ⟩
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

  p = λ x → (𝓨 x ≡ A)                 ≃⟨ i  x ⟩
            ((y : X) → 𝓨 x y ≡ A y)   ≃⟨ ii x ⟩
            ((y : X) → 𝓨 x y ≃ A y)   ■
    where
     i  = λ x → (happly (𝓨 x) A , hfe (𝓨 x) A)
     ii = λ x → Π-cong dfe dfe
                 (λ y → univalence-≃ (ua 𝓤)
                 (𝓨 x y) (A y))

  e : fiber 𝓨 A ≃ is-representable A
  e = Σ-cong p

  γ : is-subsingleton (fiber 𝓨 A)
  γ = equiv-to-subsingleton e (being-representable-is-subsingleton dfe A)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="universelifting"></a> Universe lifting

Universes are not cumulative on the nose in Agda, in the sense that
from

   > `X : 𝓤`

we would get that

   > `X : 𝓤⁺`

or that

   > `X : 𝓤 ⊔ 𝓥`.

Instead we work with embeddings of universes into larger universes.

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
\end{code}

The functions `Lift`, `lift` and `lower` have the following types:

\begin{code}
type-of-Lift  :             type-of (Lift  {𝓤} 𝓥)       ≡ (𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
type-of-lift  : {X : 𝓤 ̇ } → type-of (lift  {𝓤} {𝓥} {X}) ≡ (X → Lift 𝓥 X)
type-of-lower : {X : 𝓤 ̇ } → type-of (lower {𝓤} {𝓥} {X}) ≡ (Lift 𝓥 X → X)

type-of-Lift  = refl _
type-of-lift  = refl _
type-of-lower = refl _
\end{code}

The induction and recursion principles are as follows:

\begin{code}
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
performed with induction, but actually hold on the nose by the so-called [`η` rule
for
records](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion):

\begin{code}
lower-lift : {X : 𝓤 ̇ } (x : X) → lower {𝓤} {𝓥} (lift x) ≡ x
lower-lift = refl


lift-lower : {X : 𝓤 ̇ } (l : Lift 𝓥 X) → lift (lower l) ≡ l
lift-lower = refl


Lift-≃ : (X : 𝓤 ̇ ) → Lift 𝓥 X ≃ X
Lift-≃ {𝓤} {𝓥} X = invertibility-gives-≃ lower
                     (lift , lift-lower , lower-lift {𝓤} {𝓥})


≃-Lift : (X : 𝓤 ̇ ) → X ≃ Lift 𝓥 X
≃-Lift {𝓤} {𝓥} X = invertibility-gives-≃ lift
                     (lower , lower-lift {𝓤} {𝓥} , lift-lower)
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
universe-embedding-criterion : is-univalent 𝓤
                             → is-univalent (𝓤 ⊔ 𝓥)
                             → (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
                             → ((X : 𝓤 ̇ ) → f X ≃ X)
                             → is-embedding f

universe-embedding-criterion {𝓤} {𝓥} ua ua' f e = embedding-criterion f γ
 where
  fe : dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  fe = univalence-gives-dfunext ua'

  fe₀ : dfunext 𝓤 𝓤
  fe₀ = lower-dfunext 𝓥 𝓥 𝓤 𝓤 fe

  fe₁ : dfunext 𝓤 (𝓤 ⊔ 𝓥)
  fe₁ = lower-dfunext 𝓥 𝓥 𝓤 (𝓤 ⊔ 𝓥) fe

  γ : (X X' : 𝓤 ̇ ) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' =  (f X ≡ f X')  ≃⟨ i   ⟩
            (f X ≃ f X')  ≃⟨ ii  ⟩
            (X ≃ X')      ≃⟨ iii ⟩
            (X ≡ X')      ■
   where
    i   = univalence-≃ ua' (f X) (f X')
    ii  = Eq-Eq-cong' fe fe fe fe fe fe₀ fe₁ fe fe₀ fe₀ fe₀ fe₀ (e X) (e X')
    iii = ≃-sym (univalence-≃ ua X X')
\end{code}

In particular, the function `Lift` is an embedding:

\begin{code}
Lift-is-embedding : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥)
                  → is-embedding (Lift {𝓤} 𝓥)

Lift-is-embedding {𝓤} {𝓥} ua ua' = universe-embedding-criterion {𝓤} {𝓥} ua ua'
                                    (Lift 𝓥) Lift-≃
\end{code}

Thirdly, we have a generalization of `univalence→`
from a single universe to a pair of universes. We work with two
symmetrical versions, where the second is derived from the first.
We use an [anonymous
module](https://agda.readthedocs.io/en/latest/language/module-system.html#anonymous-modules)
to assume univalence in the following couple of construction:

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
     e Y = (X ≃ Y)                 ≃⟨ i   ⟩
           (Y ≃ X)                 ≃⟨ ii  ⟩
           (Lift 𝓤 Y ≃ Lift 𝓥 X)   ≃⟨ iii ⟩
           (Lift 𝓤 Y ≡ Lift 𝓥 X)   ■
      where
       i   = ≃-Sym fe₀ fe₁ fe
       ii  = Eq-Eq-cong' fe₁ fe fe₂ fe₁ fe fe fe fe₃
               fe fe fe fe (≃-Lift Y) (≃-Lift X)
       iii =  ≃-sym (univalence-≃ ua' (Lift 𝓤 Y) (Lift 𝓥 X))

     d : (Σ \(Y : 𝓥 ̇ ) → X ≃ Y) ≃ (Σ \(Y : 𝓥 ̇ ) → Lift 𝓤 Y ≡ Lift 𝓥 X)
     d = Σ-cong e

     j : is-subsingleton (Σ \(Y : 𝓥 ̇ ) → Lift 𝓤 Y ≡ Lift 𝓥 X)
     j = Lift-is-embedding ua ua' (Lift 𝓥 X)

     s : is-subsingleton (Σ \(Y : 𝓥 ̇ ) → X ≃ Y)
     s = equiv-to-subsingleton d j


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
univalence→'' : is-univalent (𝓤 ⊔ 𝓥)
              → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)

univalence→'' ua = univalence→' ua ua


univalence→''-dual : is-univalent (𝓤 ⊔ 𝓥)
                   → (Y : 𝓤 ̇ ) → is-subsingleton (Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)

univalence→''-dual ua = univalence→'-dual ua ua
\end{code}

The first one is applied to get the following, where `Y` lives in a
universe above that of `X`:

\begin{code}
G↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (X : 𝓤 ̇ ) (A : (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y) → 𝓦 ̇ )
     → A (Lift 𝓥 X , ≃-Lift X) → (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A (Y , e)

G↑-≃ {𝓤} {𝓥} ua X A a Y e = transport A p a
 where
  t : Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y
  t = (Lift 𝓥 X , ≃-Lift X)

  p : t ≡ (Y , e)
  p = univalence→'' {𝓤} {𝓥} ua X t (Y , e)


H↑-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (X : 𝓤 ̇ ) (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → A (Lift 𝓥 X) (≃-Lift X) → (Y : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A Y e

H↑-≃ ua X A = G↑-≃ ua X (Σ-induction A)
\end{code}

*Exercise*. [Formulate and prove](HoTT-UF-Agda.html#someexercisessol) the equations for `G↑-≃` and `H↑-≃`
 corresponding to those for `G-≃` and `H-≃`.

The difference with [`H-≃`](HoTT-UF-Agda.html-H-≃) is that here, to get
the conclusion, we need to assume

   > `A (Lift 𝓥 X) (≃-Lift X)`

rather than

   > `A X (id-≃)`.

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
lift-is-hae {𝓤} {𝓥} X = lower ,
                        lower-lift {𝓤} {𝓥} ,
                        lift-lower ,
                        λ x → refl (refl (lift x))
\end{code}

Hence all invertible maps going up universe levels are half adjoint
equivalences:

\begin{code}
equivs-are-haes↑ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ̇ } {Y : 𝓤 ⊔ 𝓥 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f

equivs-are-haes↑ {𝓤} {𝓥} ua {X} {Y} = J↑-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f)
                                       lift-is-hae X Y
\end{code}

We have a dual development with the universes going down, where we
consider `lower` in place of `lift`:

\begin{code}
G↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (Y : 𝓤 ̇ ) (A : (Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y) → 𝓦 ̇ )
     → A (Lift 𝓥 Y , Lift-≃ Y) → (X : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A (X , e)

G↓-≃ {𝓤} {𝓥} ua Y A a X e = transport A p a
 where
  t : Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y
  t = (Lift 𝓥 Y , Lift-≃ Y)

  p : t ≡ (X , e)
  p = univalence→'-dual {𝓤} {𝓤 ⊔ 𝓥} ua ua Y t (X , e)


H↓-≃ : is-univalent (𝓤 ⊔ 𝓥)
     → (Y : 𝓤 ̇ ) (A : (X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
     → A (Lift 𝓥 Y) (Lift-≃ Y) → (X : 𝓤 ⊔ 𝓥 ̇ ) (e : X ≃ Y) → A X e

H↓-≃ ua Y A = G↓-≃ ua Y (Σ-induction A)


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
lower-is-hae {𝓤} {𝓥} X = lift ,
                         lift-lower ,
                         lower-lift {𝓤} {𝓥} ,
                         (λ x → refl (refl (lower x)))

equivs-are-haes↓ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ⊔ 𝓥 ̇ } {Y : 𝓤 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f

equivs-are-haes↓ {𝓤} {𝓥} ua {X} {Y} = J↓-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f)
                                       lower-is-hae X Y
\end{code}

A crucial example of an equivalence "going down one universe" is
`Id→Eq X Y`. This is because the identity type `X ≡ Y` lives in the
successor universe `𝓤 ⁺` if `X` and `Y` live in `𝓤`, whereas the
equivalence type `X ≃ Y` lives in the same universe as `X` and
`Y`. Hence we can apply the above function `invertibles-are-haes↓` to
`Id→Eq X Y` to conclude that it is a half adjoint equivalence:

\begin{code}
Id→Eq-is-hae' : is-univalent 𝓤 → is-univalent (𝓤 ⁺)
              → {X Y : 𝓤 ̇ } → is-hae (Id→Eq X Y)

Id→Eq-is-hae' ua ua⁺ {X} {Y} = equivs-are-haes↓ ua⁺ (Id→Eq X Y) (ua X Y)
\end{code}

We can be parsimonious with the uses of univalence by instead using
`invertibles-are-haes`, which doesn't require univalence. However, that
`Id→Eq` is invertible of course requires univalence.

\begin{code}
Id→Eq-is-hae : is-univalent 𝓤
             → {X Y : 𝓤 ̇ } → is-hae (Id→Eq X Y)

Id→Eq-is-hae ua {X} {Y} = invertibles-are-haes (Id→Eq X Y)
                           (equivs-are-invertible (Id→Eq X Y) (ua X Y))
\end{code}

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
example, `is-inhabited` defined [below](HoTT-UF-Agda.html#truncation)
is a global property of type `{𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⁺ ̇ `.  Hence we
prove something more general, where in this example we take `F 𝓤 = 𝓤 ⁺`.

\begin{code}
global-≃-ap' : Univalence
             → (F : Universe → Universe)
             → (A : {𝓤 : Universe} → 𝓤 ̇ → (F 𝓤) ̇ )
             → ({𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X))
             → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y

global-≃-ap' {𝓤} {𝓥} ua F A φ X Y e =

  A X          ≃⟨ φ X                                   ⟩
  A (Lift 𝓥 X) ≃⟨ Id→Eq (A (Lift 𝓥 X)) (A (Lift 𝓤 Y)) q ⟩
  A (Lift 𝓤 Y) ≃⟨ ≃-sym (φ Y)                           ⟩
  A Y          ■
 where
  d : Lift 𝓥 X ≃ Lift 𝓤 Y
  d = Lift 𝓥 X ≃⟨ Lift-≃ X         ⟩
      X        ≃⟨ e                ⟩
      Y        ≃⟨ ≃-sym (Lift-≃ Y) ⟩
      Lift 𝓤 Y ■

  p : Lift 𝓥 X ≡ Lift 𝓤 Y
  p = Eq→Id (ua (𝓤 ⊔ 𝓥)) (Lift 𝓥 X) (Lift 𝓤 Y) d

  q : A (Lift 𝓥 X) ≡ A (Lift 𝓤 Y)
  q = ap A p
\end{code}

The first claim follows with `F = id`:

\begin{code}
global-≃-ap ua = global-≃-ap' ua id
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="subtypeclassifier"></a> The subtype classifier and other classifiers

A subtype of a type `Y` is a type `X` *together* with an embedding of `X` into `Y`:

\begin{code}
subtypes-of : 𝓤 ̇ → 𝓤 ⁺ ̇
subtypes-of {𝓤} Y = Σ \(X : 𝓤 ̇ ) → X ↪ Y
\end{code}

The type `Ω 𝓤` of subsingletons in the universe `𝓤` is the subtype
classifier of types in `𝓤`, in the sense that we have a canonical
equivalence

   > `subtypes-of Y ≃ (Y → Ω 𝓤)`

for any type `Y : 𝓤`. We will derive this from something
more general.  We defined embeddings to be maps whose fibers are
all subsingletons. We can replace `is-subsingleton` by an arbitrary
property `P` of — or even structure on — types.

The following generalizes the [slice
constructor](HoTT-UF-Agda.html#typeclassifier) `_/_`:

\begin{code}
_/[_]_ : (𝓤 : Universe) → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 /[ P ] Y = Σ \(X : 𝓤 ̇ ) → Σ \(f : X → Y) → (y : Y) → P (fiber f y)


χ-special : (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ ) → 𝓤 /[ P ] Y  → (Y → Σ P)
χ-special P Y (X , f , φ) y = fiber f y , φ y


is-special-map-classifier : (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-special-map-classifier {𝓤} P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)
\end{code}

If a universe is a map classifier then `Σ P` is the classifier of maps
with `P`-fibers, for any `P : 𝓤  → 𝓥`:

\begin{code}
mc-gives-sc : is-map-classifier 𝓤
            → (P : 𝓤 ̇ → 𝓥 ̇ ) → is-special-map-classifier P

mc-gives-sc {𝓤} s P Y = γ
 where
  e = (𝓤 /[ P ] Y)                               ≃⟨ ≃-sym a ⟩
      (Σ \(σ : 𝓤 / Y) → (y : Y) → P ((χ Y) σ y)) ≃⟨ ≃-sym b ⟩
      (Σ \(A : Y → 𝓤 ̇ ) → (y : Y) → P (A y))     ≃⟨ ≃-sym c ⟩
      (Y → Σ P)                                  ■
   where
    a = Σ-assoc
    b = Σ-change-of-variable (λ A → Π (P ∘ A)) (χ Y) (s Y)
    c = ΠΣ-distr-≃

  observation : χ-special P Y ≡ Eq→fun e
  observation = refl _

  γ : is-equiv (χ-special P Y)
  γ = Eq→fun-is-equiv e
\end{code}

Therefore we have the following canonical equivalence:

\begin{code}
special-map-classifier : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                       → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                       → 𝓤 /[ P ] Y ≃ (Y → Σ P)

special-map-classifier {𝓤} ua fe P Y =
 χ-special P Y , mc-gives-sc (universes-are-map-classifiers ua fe) P Y
\end{code}

In particular, considering `P = is-subsingleton`, we get the promised
fact that `Ω` is the subtype classifier:

\begin{code}
Ω-is-subtype-classifier : Univalence
                        → (Y : 𝓤 ̇ ) → subtypes-of Y ≃ (Y → Ω 𝓤)

Ω-is-subtype-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                  (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                  is-subsingleton
\end{code}

It follows that the type of subtypes of `Y` is always a set, even if
`Y` is not a set:

\begin{code}
subtypes-form-set : Univalence → (Y : 𝓤 ̇ ) → is-set (subtypes-of Y)
subtypes-form-set {𝓤} ua Y = equiv-to-set
                              (Ω-is-subtype-classifier ua Y)
                              (powersets-are-sets
                                (univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                (univalence-gives-dfunext (ua 𝓤))
                                (univalence-gives-propext (ua 𝓤)))
\end{code}

We now consider `P = is-singleton` and the type of singletons:

\begin{code}
𝓢 : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓢 𝓤 = Σ \(S : 𝓤 ̇ ) → is-singleton S


equiv-classification : Univalence
                     → (Y : 𝓤 ̇ ) → (Σ \(X : 𝓤 ̇ ) → X ≃ Y) ≃ (Y → 𝓢 𝓤)

equiv-classification {𝓤} ua = special-map-classifier (ua 𝓤)
                               (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                               is-singleton
\end{code}

With this we can derive a [fact we already
know](HoTT-UF-Agda.html#unicharac), as follows.  First the type of
singletons (in a universe) is itself a singleton (in the next
universe):

\begin{code}
the-singletons-form-a-singleton : propext 𝓤 → dfunext 𝓤 𝓤 → is-singleton (𝓢 𝓤)
the-singletons-form-a-singleton {𝓤} pe fe = c , φ
 where
  i : is-singleton (Lift 𝓤 𝟙)
  i = equiv-to-singleton (Lift-≃ 𝟙) 𝟙-is-singleton

  c : 𝓢 𝓤
  c = Lift 𝓤 𝟙 , i

  φ : (x : 𝓢 𝓤) → c ≡ x
  φ (S , s) = to-Σ-≡ (p , being-singleton-is-subsingleton fe _ _)
   where
    p : Lift 𝓤 𝟙 ≡ S
    p = pe (singletons-are-subsingletons (Lift 𝓤 𝟙) i)
           (singletons-are-subsingletons S s)
           (λ _ → center S s) (λ _ → center (Lift 𝓤 𝟙) i)
\end{code}

What we [already knew](HoTT-UF-Agda.html#unicharac) is this:

\begin{code}
univalence-→-again : Univalence
                   → (Y : 𝓤 ̇ ) → is-singleton (Σ \(X : 𝓤 ̇ ) → X ≃ Y)

univalence-→-again {𝓤} ua Y = equiv-to-singleton (equiv-classification ua Y) i
 where
  i : is-singleton (Y → 𝓢 𝓤)
  i = univalence-gives-vvfunext' (ua 𝓤) (ua (𝓤 ⁺))
        (λ y → the-singletons-form-a-singleton
                (univalence-gives-propext (ua 𝓤))
                (univalence-gives-dfunext (ua 𝓤)))
\end{code}

*Exercise*.
[(1)](HoTT-UF-Agda.html#pointed-types)
Show that the retractions into `Y` are classified by
the type `Σ \(A : 𝓤 ̇ ) → A` of pointed types.
[(2)](HoTT-UF-Agda.html#surjections-into) After we have
defined [propositional truncations](HoTT-UF-Agda.html#truncation) and
surjections, show that the surjections into `Y` are classified by the
type `Σ \(A : 𝓤 ̇ ) → ∥ A ∥` of inhabited types.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="magmaequivalences"></a> Magma equivalences

We now define magma equivalences and show that the type of magma
equivalences is identified with the type of magma isomorphisms. In the
next section, which proves a *structure identity principles*, we apply
this to characterize magma equality and equality of other mathematical
structures in terms of equivalences of underlying types.

For simplicity we assume global univalence here.

\begin{code}
module magma-equivalences (ua : Univalence) where

 open magmas

 dfe : global-dfunext
 dfe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua
\end{code}

The magma homomorphism and isomorphism conditions are subsingleton
types by virtue of the fact that the underlying type of a magma is a
set by definition.

\begin{code}
 being-magma-hom-is-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                 → is-subsingleton (is-magma-hom M N f)

 being-magma-hom-is-subsingleton M N f =
  Π-is-subsingleton dfe
   (λ x → Π-is-subsingleton dfe
   (λ y → magma-is-set N (f (x ·⟨ M ⟩ y)) (f x ·⟨ N ⟩ f y)))


 being-magma-iso-is-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                 → is-subsingleton (is-magma-iso M N f)

 being-magma-iso-is-subsingleton M N f (h , g , k , η , ε) (h' , g' , k' , η' , ε') = γ
  where
   p : h ≡ h'
   p = being-magma-hom-is-subsingleton M N f h h'

   q : g ≡ g'
   q = dfe (λ y → g y          ≡⟨ (ap g (ε' y))⁻¹ ⟩
                  g (f (g' y)) ≡⟨ η (g' y)        ⟩
                  g' y         ∎)

   i : is-subsingleton (is-magma-hom N M g' × (g' ∘ f ∼ id) × (f ∘ g' ∼ id))
   i = ×-is-subsingleton
         (being-magma-hom-is-subsingleton N M g')
         (×-is-subsingleton
            (Π-is-subsingleton dfe (λ x → magma-is-set M (g' (f x)) x))
            (Π-is-subsingleton dfe (λ y → magma-is-set N (f (g' y)) y)))

   γ : (h , g , k , η , ε) ≡ (h' , g' , k' , η' , ε')
   γ = to-×-≡ (p , to-Σ-≡ (q , i _ _))
\end{code}

By a magma equivalence we mean an equivalence which is a magma
homomorphism. This notion is again a subsingleton type.

\begin{code}
 is-magma-equiv : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-equiv M N f = is-equiv f × is-magma-hom M N f


 being-magma-equiv-is-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                   → is-subsingleton (is-magma-equiv M N f)

 being-magma-equiv-is-subsingleton M N f =
  ×-is-subsingleton
   (being-equiv-is-subsingleton dfe dfe f)
   (being-magma-hom-is-subsingleton M N f)
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
   k a b = g (a ·⟨ N ⟩ b)             ≡⟨ ap₂ (λ a b → g (a ·⟨ N ⟩ b)) ((ε a)⁻¹)
                                             ((ε b)⁻¹)                          ⟩
           g (f (g a) ·⟨ N ⟩ f (g b)) ≡⟨ ap g ((h (g a) (g b))⁻¹)               ⟩
           g (f (g a ·⟨ M ⟩ g b))     ≡⟨ η (g a ·⟨ M ⟩ g b)                     ⟩
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
                           (being-magma-iso-is-subsingleton M N f)
                           (being-magma-equiv-is-subsingleton M N f)
                           (magma-isos-are-magma-equivs M N f ,
                            magma-equivs-are-magma-isos M N f)
\end{code}

And hence they are equal by univalence.

\begin{code}
 magma-iso-charac' : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                   → is-magma-iso M N f ≡ is-magma-equiv M N f

 magma-iso-charac' M N f = Eq→Id (ua (universe-of ⟨ M ⟩))
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

It follows from the results of this and the next section that magma
equality amounts to magma isomorphism.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="sip"></a> Equality of mathematical structures

Independently of any choice of foundation, we regard two groups to be
the same, for all mathematical purposes, if they are isomorphic.
Likewise, we consider two topological spaces to be the same if they
are homeomorphic, two metric spaces to be the same if they are
isometric, two categories to be the same if they are equivalent, and
so on.

With Voevodsky's univalence axiom, we can *prove* that these notions
of sameness are automatically captured by Martin-Löf's identity
type. In particular, properties of groups are automatically invariant
under isomorphism, properties of topological spaces are automatically
invariant under homeomorphism, properties of metric spaces are
automatically invariant under isometry, properties of categories are
automatically invariant under equivalence, and so on, simply because,
by design, properties are invariant under the notion of equality given
by the identity type. In other foundations, the lack of such automatic
invariance creates [practical
difficulties](https://mathoverflow.net/questions/336191/cauchy-reals-and-dedekind-reals-satisfy-the-same-mathematical-theorems/).

A *structure identity principle* describes the identity type of types
of mathematical structures in terms of equivalences of
underlying types, relying on univalence.  The first published
structure identity principle, for a large class of algebraic
structures, is [[Coquand and
Danielsson]](https://www.sciencedirect.com/science/article/pii/S0019357713000694). The
HoTT book (section 9.8) has a categorical version, whose formulation
is attributed to Peter Aczel.

Here we formulate and prove a variation for types equipped with
structure. We consider several versions:

 1. One for raw structures subject to no axioms, such as ∞-magmas and
    pointed types.

 1. One that adds axioms to a structure, so as to e.g. get an
    automatic characterization of magma identifications from a
    characterization of ∞-magma identifications.

 1. One that joins two kinds of structure, so as to e.g. get an
    automatic characterization of identifications of pointed ∞-magmas
    from characterizations of identifications for pointed types and
    for ∞-magmas.

 1. In particular, adding axioms to pointed ∞-magmas we get monoids
    with an automatic characterization of their identifications.

 1. And then adding an axiom to monoids we get groups, again with
    an automatic characterization of their identitifications.

We also apply theses ideas to characterize identifications of metric
spaces, topological spaces, graphs, partially ordered sets, categories
and more.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="sns"></a> A structure identity principle for a standard notion of structure

\begin{code}
module sip where
\end{code}

We consider mathematical structures specified by a function

   > `S : 𝓤 ̇ → 𝓥 ̇ `

and we consider types `X : 𝓤` equipped with such structure `s : S X`,
collected in the type

   > `Σ \(X : 𝓤) → S X`,

which, as we have seen, can be abbreviated as

   > `Σ S`.

For example, for the type of ∞-magmas we will take `𝓥 = 𝓤` and

   > `S X = X → X → X`.

Our objective is to describe the identity type `Id (Σ S) A B`, in
favourable circumstances, in terms of equivalences of the underlying
types `⟨ A ⟩` and `⟨ B ⟩` of `A B : Σ S`.

\begin{code}
 ⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
 ⟨ X , s ⟩ = X

 structure : {S : 𝓤 ̇ → 𝓥 ̇ } (A : Σ S) → S ⟨ A ⟩
 structure (X , s) = s
\end{code}

Our favourable circumstances will be given by data

   > `ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ `

   > `ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)`

The idea is that

  * `ι` describes favourable equivalences, which will be called homomorphisms, and
  * `ρ` then stipulates that all identity equivalences are homomorphisms.

We require that any two structures on the same type making the identity
equivalence a homomorphism must be equal in a canonical way:

 * The canonical map

   > `s ≡ t  → ι (X , s) (X , t) (id-≃ X)`

   defined by induction on identifications by

   > `refl s ↦ ρ (X , s)`

   must be an equivalence for all `X : 𝓤 ` and `s t : S X` .

This may sound a bit abstract at this point, but in practical examples
of interest it is easy to fulfill these requirements, as we will
illustrate soon.

We first define the canonical map:

\begin{code}
 canonical-map : {S : 𝓤 ̇ → 𝓥 ̇ }
                 (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                 (ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
                 {X : 𝓤 ̇ }
                 (s t : S X)

               → s ≡ t → ι (X , s) (X , t) (id-≃ X)

 canonical-map ι ρ {X} s s (refl s) = ρ (X , s)
\end{code}

We refer to such favourable data as a *standard notion of structure*
and collect them in the type

   > `SNS S 𝓦`

as follows:

\begin{code}
 SNS : (𝓤 ̇ → 𝓥 ̇ ) → (𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇

 SNS {𝓤} {𝓥} S 𝓦 = Σ \(ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                  → Σ \(ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
                  → {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
\end{code}

We write `homomorphic` for the first projection (we don't need
names for the other two projections):

\begin{code}
 homomorphic : {S : 𝓤 ̇ → 𝓥 ̇ } → SNS S 𝓦
             → (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇

 homomorphic (ι , ρ , θ) = ι
\end{code}

For example, when `S` specifies ∞-magma structure, we will have
that `homomorphic σ A B (f , i)` amounts to `f` being a magma
homomorphism.

We then collect the homomorphic equivalences of `A B : Σ S`, assuming
that `S` is a standard notion of structure, witnessed by `σ`, in a type

   > `A ≃[ σ ] B`.

Notice that only the first component of `σ`, namely `homomorphic σ`, is
used in the definition:

\begin{code}
 _≃[_]_ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → SNS S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇

 A ≃[ σ ] B = Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
            → Σ \(i : is-equiv f) → homomorphic σ A B (f , i)


 Id→homEq : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
          → (A B : Σ S) → (A ≡ B) → (A ≃[ σ ] B)

 Id→homEq (_ , ρ , _) A A (refl A) = id , id-is-equiv ⟨ A ⟩ , ρ A
\end{code}

With this we are ready to prove the promised characterization of
identity on `Σ S`:

\begin{code}
 homomorphism-lemma : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                      (A B : Σ S) (p : ⟨ A ⟩ ≡ ⟨ B ⟩)
                    →
                      (transport S p (structure A) ≡ structure B)
                    ≃  homomorphic σ A B (Id→Eq ⟨ A ⟩ ⟨ B ⟩ p)

 homomorphism-lemma (ι , ρ , θ) (X , s) (X , t) (refl X) = γ
  where
   γ : (s ≡ t) ≃ ι (X , s) (X , t) (id-≃ X)
   γ = (canonical-map ι ρ s t , θ s t)


 characterization-of-≡ : is-univalent 𝓤
                       → {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                       → (A B : Σ S)

                       → (A ≡ B) ≃ (A ≃[ σ ] B)

 characterization-of-≡ ua {S} σ A B =

    (A ≡ B)                                                              ≃⟨ i   ⟩
    (Σ \(p : ⟨ A ⟩ ≡ ⟨ B ⟩) → transport S p (structure A) ≡ structure B) ≃⟨ ii  ⟩
    (Σ \(p : ⟨ A ⟩ ≡ ⟨ B ⟩) → ι A B (Id→Eq ⟨ A ⟩ ⟨ B ⟩ p))               ≃⟨ iii ⟩
    (Σ \(e : ⟨ A ⟩ ≃ ⟨ B ⟩) → ι A B e)                                   ≃⟨ iv  ⟩
    (A ≃[ σ ] B)                                                         ■

  where
   ι   = homomorphic σ
   i   = Σ-≡-≃ A B
   ii  = Σ-cong (homomorphism-lemma σ A B)
   iii = ≃-sym (Σ-change-of-variable (ι A B) (Id→Eq ⟨ A ⟩ ⟨ B ⟩) (ua ⟨ A ⟩ ⟨ B ⟩))
   iv  = Σ-assoc
\end{code}

This equivalence is pointwise equal to `Id→homEq`, and hence `Id→homEq`
is itself an equivalence:

\begin{code}
 Id→homEq-is-equiv : (ua : is-univalent 𝓤) {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
                   → (A B : Σ S) → is-equiv (Id→homEq σ A B)

 Id→homEq-is-equiv ua {S} σ A B = γ
  where
   h : (A B : Σ S) → Id→homEq σ A B ∼ Eq→fun (characterization-of-≡ ua σ A B)
   h A A (refl A) = refl _

   γ : is-equiv (Id→homEq σ A B)
   γ = equivs-closed-under-∼
       (Eq→fun-is-equiv (characterization-of-≡ ua σ A B))
       (h A B)
\end{code}

This concludes the module `sip`, and we now consider some examples of uses of this.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="infty-magmas"></a> ∞-Magmas

\begin{code}
module ∞-magma-identity {𝓤 : Universe} where

 open sip

 ∞-magma-structure : 𝓤 ̇ → 𝓤 ̇
 ∞-magma-structure X = X → X → X

 ∞-Magma : 𝓤 ⁺ ̇
 ∞-Magma = Σ \(X : 𝓤 ̇ ) → ∞-magma-structure X

 sns-data : SNS ∞-magma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : ∞-Magma) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , _·_) (Y , _*_) (f , _) = (λ x x' → f (x · x')) ≡ (λ x x' → f x * f x')

   ρ : (A : ∞-Magma) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , _·_) = refl _·_

   h : {X : 𝓤 ̇ } {_·_ _*_ : ∞-magma-structure X}
     → canonical-map ι ρ _·_ _*_ ∼ 𝑖𝑑 (_·_ ≡ _*_)

   h (refl _·_) = refl (refl _·_)


   θ : {X : 𝓤 ̇ } (_·_ _*_ : ∞-magma-structure X)
     → is-equiv (canonical-map ι ρ _·_ _*_)

   θ _·_ _*_ = equivs-closed-under-∼ (id-is-equiv (_·_ ≡ _*_)) h


 _≅_ : ∞-Magma → ∞-Magma → 𝓤 ̇

 (X , _·_) ≅ (Y , _*_) =

           Σ \(f : X → Y) → is-equiv f
                          × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))


 characterization-of-∞-Magma-≡ : is-univalent 𝓤
                               → (A B : ∞-Magma)

                               → (A ≡ B) ≃ (A ≅ B)

 characterization-of-∞-Magma-≡ ua = characterization-of-≡ ua sns-data
\end{code}

The above equivalence is characterized by induction on identifications
as the function that maps the reflexive identification to the identity
equivalence:

\begin{code}
 characterization-of-characterization-of-∞-Magma-≡ :

    (ua : is-univalent 𝓤) (A : ∞-Magma)
  →
    Eq→fun (characterization-of-∞-Magma-≡ ua A A) (refl A)
  ≡
    (𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _)

 characterization-of-characterization-of-∞-Magma-≡ ua A = refl _
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="adding-axioms"></a> Adding axioms

Next we want to account for situations in which axioms are
considered, for example that the underlying type is a set, or that the
monoid structure satisfies the unit and associativity laws. We do this
in a submodule, by reduction to the characterization of
identifications given in the module `sip`.

\begin{code}
module sip-with-axioms where

 open sip
\end{code}

The first construction, given `S` as above, and given
subsingleton-valued axioms for types equipped with structure specified
by `S`, builds `SNS` data on `S'` defined by

   > `S' X = Σ \(s : S X) → axioms X s`

from given `SNS` data on `S`.

For that purpose we first define a forgetful map `Σ S' → Σ S` and
an underlying-type function `Σ S → 𝓤`:

\begin{code}
 [_] : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → axioms X s) → Σ S

 [ X , s , _ ] = (X , s)


 ⟪_⟫ : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → axioms X s) → 𝓤 ̇

 ⟪ X , _ , _ ⟫ = X
\end{code}

In the following construction:

 * For `ι'` and `ρ'` we use `ι` and `ρ` ignoring the axioms.

 * For `θ'` we need more work, but the essence of the construction is the
   fact that the projection

   > `S' X → S X`

   that forgets the axioms is an embedding precisely because the
   axioms are subsingleton-valued.

\begin{code}
 add-axioms : {S : 𝓤 ̇ → 𝓥 ̇ }
              (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
            → ((X : 𝓤 ̇ ) (s : S X) → is-subsingleton (axioms X s))
            → SNS S 𝓣
            → SNS (λ X → Σ \(s : S X) → axioms X s) 𝓣

 add-axioms {𝓤} {𝓥} {𝓦} {𝓣} {S} axioms i (ι , ρ , θ) = ι' , ρ' , θ'
  where
   S' : 𝓤 ̇ → 𝓥 ⊔ 𝓦  ̇
   S' X = Σ \(s : S X) → axioms X s

   ι' : (A B : Σ S') → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓣 ̇
   ι' A B = ι [ A ] [ B ]

   ρ' : (A : Σ S') → ι' A A (id-≃ ⟨ A ⟩)
   ρ' A = ρ [ A ]

   θ' : {X : 𝓤 ̇ } (s' t' : S' X) → is-equiv (canonical-map ι' ρ' s' t')
   θ' {X} (s , a) (t , b) = γ
    where
     π : S' X → S X
     π (s , _) = s

     j : is-embedding π
     j = pr₁-embedding (i X)

     k : {s' t' : S' X} → is-equiv (ap π {s'} {t'})
     k {s'} {t'} = embedding-gives-ap-is-equiv π j s' t'

     l : canonical-map ι' ρ' (s , a) (t , b)
       ∼ canonical-map ι ρ s t ∘ ap π {s , a} {t , b}
     l (refl (s , a)) = refl (ρ (X , s))

     e : is-equiv (canonical-map ι ρ s t ∘ ap π {s , a} {t , b})
     e = ∘-is-equiv (θ s t) k

     γ : is-equiv (canonical-map ι' ρ' (s , a) (t , b))
     γ = equivs-closed-under-∼ e l

\end{code}

And with this we can formulate and prove what `add-axioms` achieves,
namely that the characterization of the identity type remains the
same, ignoring the axioms:

\begin{code}
 characterization-of-≡-with-axioms :

     is-univalent 𝓤
   → {S : 𝓤 ̇ → 𝓥 ̇ }
     (σ : SNS S 𝓣)
     (axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
   → ((X : 𝓤 ̇ ) (s : S X) → is-subsingleton (axioms X s))
   →
     (A B : Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → axioms X s)
   →
     (A ≡ B) ≃ ([ A ] ≃[ σ ] [ B ])

 characterization-of-≡-with-axioms ua σ axioms i =
   characterization-of-≡ ua (add-axioms axioms i σ)
\end{code}

And this concludes the module `sip-with-axioms`. We now consider some
examples.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="magmas-sip"></a> Magmas

\begin{code}
module magma-identity {𝓤 : Universe} where

 open sip-with-axioms

 Magma : 𝓤 ⁺ ̇
 Magma = Σ \(X : 𝓤 ̇ ) → (X → X → X) × is-set X

 _≅_ : Magma → Magma → 𝓤 ̇

 (X , _·_ , _) ≅ (Y , _*_ , _) =

               Σ \(f : X → Y) → is-equiv f
                              × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))


 characterization-of-Magma-≡ : is-univalent 𝓤
                             → (A B : Magma )

                             → (A ≡ B) ≃ (A ≅ B)

 characterization-of-Magma-≡ ua =
   characterization-of-≡-with-axioms ua
     ∞-magma-identity.sns-data
     (λ X s → is-set X)
     (λ X s → being-set-is-subsingleton (univalence-gives-dfunext ua))
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

*Exercise*. Characterize identifications of monoids along the above lines. It
 is convenient to redefine the type of monoids to an equivalent type
 in the above format of structure with axioms. The following
   developement solves this exercise.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="pointed-types"></a> Pointed types

\begin{code}
module pointed-type-identity {𝓤 : Universe} where

 open sip

 Pointed : 𝓤 ̇ → 𝓤 ̇
 Pointed X = X

 sns-data : SNS Pointed 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ Pointed) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , x₀) (Y , y₀) (f , _) = (f x₀ ≡ y₀)

   ρ : (A : Σ Pointed) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , x₀) = refl x₀

   θ : {X : 𝓤 ̇ } (x₀ x₁ : Pointed X) → is-equiv (canonical-map ι ρ x₀ x₁)
   θ x₀ x₁ = equivs-closed-under-∼ (id-is-equiv (x₀ ≡ x₁)) h
    where
     h : canonical-map ι ρ x₀ x₁ ∼ 𝑖𝑑 (x₀ ≡ x₁)
     h (refl x₀) = refl (refl x₀)


 _≅_ : Σ Pointed → Σ Pointed → 𝓤 ̇
 (X , x₀) ≅ (Y , y₀) = Σ \(f : X → Y) → is-equiv f × (f x₀ ≡ y₀)


 characterization-of-pointed-type-≡ : is-univalent 𝓤
                                    → (A B : Σ Pointed)

                                    → (A ≡ B) ≃ (A ≅ B)

 characterization-of-pointed-type-≡ ua = characterization-of-≡ ua sns-data
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="combining-structures"></a> Combining two mathematical structures

We now show how to join two mathematics structures so as to obtain a
characterization of the identifications of the join from the
characterization of the equalities of the structures. For example, we
build the characterization of identifications of pointed ∞-magmas from
the characterizations of the identifications of pointed types and the
characterization of the identifications of magmas. Moreover, adding
axioms, we get a characterization of identifications of monoids which
amounts to the characterization of identifications of pointed
∞-magmas. Further adding an axiom, we get an automatic
characterization of group identifications.

\begin{code}
module sip-join where
\end{code}

We begin with the following technical lemma:

\begin{code}
 technical-lemma :

     {X : 𝓤 ̇ } {A : X → X → 𝓥 ̇ }
     {Y : 𝓦 ̇ } {B : Y → Y → 𝓣 ̇ }
     (f : (x₀ x₁ : X) → x₀ ≡ x₁ → A x₀ x₁)
     (g : (y₀ y₁ : Y) → y₀ ≡ y₁ → B y₀ y₁)
   → ((x₀ x₁ : X) → is-equiv (f x₀ x₁))
   → ((y₀ y₁ : Y) → is-equiv (g y₀ y₁))

   → (z₀ z₁ : X × Y) → is-equiv (λ (p : z₀ ≡ z₁) → f (pr₁ z₀) (pr₁ z₁) (ap pr₁ p) ,
                                                   g (pr₂ z₀) (pr₂ z₁) (ap pr₂ p))

 technical-lemma {𝓤} {𝓥} {𝓦} {𝓣} {X} {A} {Y} {B} f g i j (x₀ , y₀) = γ
  where
   module _ (z₁ : X × Y) where
     x₁ = pr₁ z₁
     y₁ = pr₂ z₁

     r : (x₀ , y₀) ≡ (x₁ , y₁) → A x₀ x₁ × B y₀ y₁
     r p = f x₀ x₁ (ap pr₁ p) , g y₀ y₁ (ap pr₂ p)

     f' : (a : A x₀ x₁) → x₀ ≡ x₁
     f' = inverse (f x₀ x₁) (i x₀ x₁)

     g' : (b : B y₀ y₁) → y₀ ≡ y₁
     g' = inverse (g y₀ y₁) (j y₀ y₁)

     s : A x₀ x₁ × B y₀ y₁ → (x₀ , y₀) ≡ (x₁ , y₁)
     s (a , b) = to-×-≡ (f' a , g' b)

     η : (c : A x₀ x₁ × B y₀ y₁) → r (s c) ≡ c
     η (a , b) =
       r (s (a , b))                              ≡⟨ refl _ ⟩
       r (to-×-≡  (f' a , g' b))                  ≡⟨ refl _ ⟩
       (f x₀ x₁ (ap pr₁ (to-×-≡ (f' a , g' b))) ,
        g y₀ y₁ (ap pr₂ (to-×-≡ (f' a , g' b))))  ≡⟨ ii  ⟩
       (f x₀ x₁ (f' a) , g y₀ y₁ (g' b))          ≡⟨ iii ⟩
       a , b                                      ∎
      where
       ii = ap₂ (λ p q → f x₀ x₁ p , g y₀ y₁ q)
                (ap-pr₁-to-×-≡ (f' a) (g' b))
                (ap-pr₂-to-×-≡ (f' a) (g' b))
       iii = to-×-≡ (inverse-is-section (f x₀ x₁) (i x₀ x₁) a ,
                     inverse-is-section (g y₀ y₁) (j y₀ y₁) b)

   γ : ∀ z₁ → is-equiv (r z₁)
   γ = fiberwise-retractions-are-equivs (λ z₁ → A x₀ (pr₁ z₁) × B y₀ (pr₂ z₁))
         (x₀ , y₀) r (λ z₁ → (s z₁ , η z₁))
\end{code}

We consider two given mathematical structures specified by `S₀` and
`S₁`, and work with structures specified by their combination `λ X →
S₀ X × S₁ X`

\begin{code}
 variable
  𝓥₀ 𝓥₁ 𝓦₀ 𝓦₁ : Universe

 open sip

 ⟪_⟫ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
     → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X) → 𝓤 ̇

 ⟪ X , s₀ , s₁ ⟫ = X



 [_]₀ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X) → Σ S₀

 [ X , s₀ , s₁ ]₀ = (X , s₀)



 [_]₁ : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X) → Σ S₁

 [ X , s₀ , s₁ ]₁ = (X , s₁)
\end{code}

The main construction in this submodule is this:

\begin{code}
 join : {S₀ : 𝓤 ̇ → 𝓥₀ ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
      → SNS S₀ 𝓦₀
      → SNS S₁ 𝓦₁
      → SNS (λ X → S₀ X × S₁ X) (𝓦₀ ⊔ 𝓦₁)

 join {𝓤} {𝓥₀} {𝓥₁} {𝓦₀} {𝓦₁} {S₀} {S₁} (ι₀ , ρ₀ , θ₀) (ι₁ , ρ₁ , θ₁) = ι , ρ , θ
  where
   S : 𝓤 ̇ → 𝓥₀ ⊔ 𝓥₁ ̇
   S X = S₀ X × S₁ X

   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦₀ ⊔ 𝓦₁ ̇
   ι A B e = ι₀ [ A ]₀ [ B ]₀ e  ×  ι₁ [ A ]₁ [ B ]₁ e

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ A = (ρ₀ [ A ]₀ , ρ₁ [ A ]₁)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
   θ {X} (s₀ , s₁) (t₀ , t₁) = γ
    where
     c : (p : s₀ , s₁ ≡ t₀ , t₁) → ι₀ (X , s₀) (X , t₀) (id-≃ X)
                                 × ι₁ (X , s₁) (X , t₁) (id-≃ X)

     c p = (canonical-map ι₀ ρ₀ s₀ t₀ (ap pr₁ p) ,
            canonical-map ι₁ ρ₁ s₁ t₁ (ap pr₂ p))

     i : is-equiv c
     i = technical-lemma
          (canonical-map ι₀ ρ₀)
          (canonical-map ι₁ ρ₁)
          θ₀ θ₁ (s₀ , s₁) (t₀ , t₁)

     e : canonical-map ι ρ (s₀ , s₁) (t₀ , t₁) ∼ c
     e (refl (s₀ , s₁)) = refl (ρ₀ (X , s₀) , ρ₁ (X , s₁))

     γ : is-equiv (canonical-map ι ρ (s₀ , s₁) (t₀ , t₁))
     γ = equivs-closed-under-∼ i e
\end{code}

We then can characterize the identity type of structures in the join
by the following relation:

\begin{code}
 _≃⟦_,_⟧_ : {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }

          → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X)
          → SNS S₀ 𝓦₀
          → SNS S₁ 𝓦₁
          → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X)

          → 𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇

 A ≃⟦ σ₀ , σ₁ ⟧ B = Σ \(f : ⟪ A ⟫ → ⟪ B ⟫)
                  → Σ \(i : is-equiv f) → homomorphic σ₀ [ A ]₀ [ B ]₀ (f , i)
                                        × homomorphic σ₁ [ A ]₁ [ B ]₁ (f , i)
\end{code}

The following is then immediate from the join construction and the
general structure identity principle:

\begin{code}
 characterization-of-join-≡ : is-univalent 𝓤
                            → {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
                              (σ₀ : SNS S₀ 𝓦₀)  (σ₁ : SNS S₁ 𝓦₁)

                              (A B : Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X)
                            →
                              (A ≡ B) ≃ (A ≃⟦ σ₀ , σ₁ ⟧ B)

 characterization-of-join-≡ ua σ₀ σ₁ = characterization-of-≡ ua (join σ₀ σ₁)
\end{code}

This concludes the submodule. Some examples of uses of this follow.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="pointed-infty-magmas"></a> Pointed ∞-magmas

\begin{code}
module pointed-∞-magma-identity {𝓤 : Universe} where

 open sip-join

 ∞-Magma· : 𝓤 ⁺ ̇
 ∞-Magma· = Σ \(X : 𝓤 ̇ ) → (X → X → X) × X


 _≅_ : ∞-Magma· → ∞-Magma· → 𝓤 ̇

 (X ,  _·_ , x₀) ≅ (Y ,  _*_ , y₀) =

                 Σ \(f : X → Y) → is-equiv f
                                × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
                                × (f x₀ ≡ y₀)


 characterization-of-pointed-magma-≡ : is-univalent 𝓤
                                     → (A B : ∞-Magma·)

                                     → (A ≡ B) ≃ (A ≅ B)

 characterization-of-pointed-magma-≡ ua = characterization-of-join-≡ ua
                                            ∞-magma-identity.sns-data
                                            pointed-type-identity.sns-data
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="monoids-sip"></a> Monoids

In the following example, we combine joins and addition of axioms.

\begin{code}
module monoid-identity {𝓤 : Universe} (ua : is-univalent 𝓤) where

 dfe : dfunext 𝓤 𝓤
 dfe = univalence-gives-dfunext ua

 open sip
 open sip-join
 open sip-with-axioms

 monoid-structure : 𝓤 ̇ → 𝓤 ̇
 monoid-structure X = (X → X → X) × X


 monoid-axioms : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 monoid-axioms X (_·_ , e) = is-set X
                           × monoids.left-neutral  e _·_
                           × monoids.right-neutral e _·_
                           × monoids.associative     _·_

 Monoid : 𝓤 ⁺ ̇
 Monoid = Σ \(X : 𝓤 ̇ ) → Σ \(s : monoid-structure X) → monoid-axioms X s

 monoid-axioms-subsingleton : (X : 𝓤 ̇ ) (s : monoid-structure X)
                            → is-subsingleton (monoid-axioms X s)

 monoid-axioms-subsingleton X (_·_ , e) s = γ s
  where
   i : is-set X
   i = pr₁ s

   γ : is-subsingleton (monoid-axioms X (_·_ , e))
   γ = ×-is-subsingleton
         (being-set-is-subsingleton dfe)
      (×-is-subsingleton
         (Π-is-subsingleton dfe
           (λ x → i (e · x) x))
      (×-is-subsingleton
         (Π-is-subsingleton dfe
           (λ x → i (x · e) x))
         (Π-is-subsingleton dfe
           (λ x → Π-is-subsingleton dfe
           (λ y → Π-is-subsingleton dfe
           (λ z → i ((x · y) · z) (x · (y · z))))))))


 sns-data : SNS (λ X → Σ \(s : monoid-structure X) → monoid-axioms X s) 𝓤
 sns-data = add-axioms
              monoid-axioms monoid-axioms-subsingleton
              (join
                 ∞-magma-identity.sns-data
                 pointed-type-identity.sns-data)

 _≅_ : Monoid → Monoid → 𝓤 ̇

 (X , (_·_ , d) , _) ≅ (Y , (_*_ , e) , _) =

                     Σ \(f : X → Y) → is-equiv f
                                    × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
                                    × (f d ≡ e)


 characterization-of-monoid-≡ : is-univalent 𝓤
                              → (A B : Monoid)

                              → (A ≡ B) ≃ (A ≅ B)

 characterization-of-monoid-≡ ua = characterization-of-≡ ua sns-data
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="groups-sip"></a> Groups

We add an axiom to monoids to get groups.

\begin{code}
module group-identity {𝓤 : Universe} (ua : is-univalent 𝓤) where

 open sip
 open sip-with-axioms
 open monoid-identity {𝓤} ua hiding (sns-data ; _≅_)

 group-structure : 𝓤 ̇ → 𝓤 ̇
 group-structure X = Σ \(s : monoid-structure X) → monoid-axioms X s

 group-axiom : (X : 𝓤 ̇ ) → monoid-structure X → 𝓤 ̇
 group-axiom X (_·_ , e) = (x : X) → Σ \(x' : X) → (x · x' ≡ e) × (x' · x ≡ e)

 Group : 𝓤 ⁺ ̇
 Group = Σ \(X : 𝓤 ̇ ) → Σ \(s : group-structure X) → group-axiom X (pr₁ s)


 group-axiom-is-subsingleton : (X : 𝓤 ̇ )
                             → (s : group-structure X)
                             → is-subsingleton (group-axiom X (pr₁ s))

 group-axiom-is-subsingleton X ((_·_ , e) , (s , l , r , a)) = γ
  where
   i : (x : X) → is-subsingleton (Σ \(x' : X) → (x · x' ≡ e) × (x' · x ≡ e))
   i x (y , _ , q) (z , p , _) = u
    where
     t = y             ≡⟨ (r y)⁻¹          ⟩
         (y · e)       ≡⟨ ap (y ·_) (p ⁻¹) ⟩
         (y · (x · z)) ≡⟨ (a y x z)⁻¹      ⟩
         ((y · x) · z) ≡⟨ ap (_· z) q      ⟩
         (e · z)       ≡⟨ l z              ⟩
         z ∎

     u : (y , _ , q) ≡ (z , p , _)
     u = to-Σ-≡ (t , to-×-≡ (s (x · z) e _ _ , s (z · x) e _ _))

   γ : is-subsingleton (group-axiom X (_·_ , e))
   γ = Π-is-subsingleton dfe i


 sns-data : SNS (λ X → Σ \(s : group-structure X) → group-axiom X (pr₁ s)) 𝓤
 sns-data = add-axioms
             (λ X s → group-axiom X (pr₁ s)) group-axiom-is-subsingleton
             (monoid-identity.sns-data ua)


 _≅_ : Group → Group → 𝓤 ̇

 (X , ((_·_ , d) , _) , _) ≅ (Y , ((_*_ , e) , _) , _) =

            Σ \(f : X → Y) → is-equiv f
                           × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
                           × (f d ≡ e)


 characterization-of-group-≡ : is-univalent 𝓤
                             → (A B : Group)

                             → (A ≡ B) ≃ (A ≅ B)

 characterization-of-group-≡ ua = characterization-of-≡ ua sns-data
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

*Exercise*. In the case of groups, as opposed to monoids, the
 preservation of the unit follows from the preservation of the
 multiplication, and hence one can remove `f d ≡ e` from the above
 definition. Prove that

   > `(A ≅ B) ≃ (A ≅' B)`

 and hence, by transitivity,

   > `(A ≡ B) ≃ (A ≅' B)`

 where

\begin{code}
 _≅'_ : Group → Group → 𝓤 ̇

 (X , ((_·_ , d) , _) , _) ≅' (Y , ((_*_ , e) , _) , _) =

            Σ \(f : X → Y) → is-equiv f
                           × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))
\end{code}

*Exercise*. In the same way that two elements of the powerset are
 equal iff they [have the same
 elements](HoTT-UF-Agda.html#subset-extensionality), two subgroups are
 equal if and only if they have the same elements. This can be
 formulated and proved in two equivalent ways.

  1. A subgroup is an element of the powerset of the underlying set of
  the group that is closed under the group operations. So the type of
  subgroups of a given group is embedded as a subtype of the powerset
  of the underlying set and inherits the characterization of equality
  of the powerset.

  1. A subgroup of a group `G` is a group `H` *together* with a
  homomorphism `H → G` which is also an embedding. Show that this
  second definition of the type of subgroups produces a type that is
  equivalent to the previous. With this second definition, two
  subgroups `H` and `H'` are equal iff the embeddings `H → G` and `H'
  → G` can be completed to a commutative triangle by a group
  isomorphism `H → H'`, which is necessarily unique when it exists.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="slice-sip"></a> The slice type

\begin{code}
module slice-identity
        {𝓤 : Universe}
        (R : 𝓤 ̇ )
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ̇
 S X = X → R

 sns-data : SNS S 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , g) (Y , h) (f , _) = (g ≡ h ∘ f)

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , g) = refl g

   k : {X : 𝓤 ̇ } {g h : S X} → canonical-map ι ρ g h ∼ 𝑖𝑑 (g ≡ h)
   k (refl g) = refl (refl g)

   θ : {X : 𝓤 ̇ } (g h : S X) → is-equiv (canonical-map ι ρ g h)
   θ g h = equivs-closed-under-∼ (id-is-equiv (g ≡ h)) k


 _≅_  : 𝓤 / R → 𝓤 / R → 𝓤 ̇
 (X , g) ≅ (Y , h) = Σ \(f : X → Y) → is-equiv f × (g ≡ h ∘ f )


 characterization-of-/-≡ : is-univalent 𝓤
                         → (A B : 𝓤 / R)

                         → (A ≡ B) ≃ (A ≅ B)

 characterization-of-/-≡ ua = characterization-of-≡ ua sns-data
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="metric-sip"></a> Metric spaces, graphs and ordered structures

\begin{code}
module generalized-metric-space-identity
        {𝓤 𝓥 : Universe}
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → (X → X → R) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (d : X → X → R) → is-subsingleton (axioms X d))
       where

 open sip
 open sip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , d) (Y , e) (f , _) = (d ≡ λ x x' → e (f x) (f x'))

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , d) = refl d

   h : {X : 𝓤 ̇ } {d e : S X} → canonical-map ι ρ d e ∼ 𝑖𝑑 (d ≡ e)
   h (refl d) = refl (refl d)

   θ : {X : 𝓤 ̇ } (d e : S X) → is-equiv (canonical-map ι ρ d e)
   θ d e = equivs-closed-under-∼ (id-is-equiv (d ≡ e)) h


 M : 𝓤 ⁺ ⊔ 𝓥  ̇
 M = Σ \(X : 𝓤 ̇ ) → Σ \(d : X → X → R) → axioms X d

 _≅_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅ (Y , e , _) = Σ \(f : X → Y) → is-equiv f
                                            × (d ≡ λ x x' → e (f x) (f x'))

 characterization-of-M-≡ : is-univalent 𝓤
                         → (A B : M)

                         → (A ≡ B) ≃ (A ≅ B)

 characterization-of-M-≡ ua = characterization-of-≡-with-axioms ua
                                sns-data
                                axioms axiomss
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

We have the following particular cases of interest:

 1. *Metric spaces*. If `R` is a type of real numbers, then the axioms
    can be taken to be those for metric spaces, in which case `M`
    amounts to the type of metric spaces. Then the above characterizes
    metric space identification as isometry.

 1. *Graphs*. If `R` is the type of truth values, and the `axioms`
    function is constant with value *true*, then `M` amounts to the
    type of directed graphs, and the above characterizes graph
    identification as graph isomorphism. We get undirected graphs by
    requiring the relation to be symmetric in the axioms.

 1. *Partially ordered sets*. Again with `R` taken to be the type of
    truth values and suitable axioms, we get posets and other ordered
    structures, and the above says that their identifications amount
    to order isomorphisms.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="topological-sip"></a> Topological spaces

We get a [type of topological spaces](HoTT-UF-Agda.html#Top) when `R`
is the type of truth values and the axioms are appropriately chosen.

\begin{code}
module generalized-topological-space-identity
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → R) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (𝓞 : (X → R) → R) → is-subsingleton (axioms X 𝓞))
       where

 open sip
 open sip-with-axioms
\end{code}

When `R` is the type of truth values, the type `(X → R)` is the
powerset of `X`, and membership amounts to function application:

\begin{code}
 ℙ : 𝓦 ̇ → 𝓥 ⊔ 𝓦 ̇
 ℙ X = X → R

 _∊_ : {X : 𝓦 ̇ } → X → ℙ X → R
 x ∊ A = A x

 inverse-image : {X Y : 𝓤 ̇ } → (X → Y) → ℙ Y → ℙ X
 inverse-image f B = λ x → f x ∊ B

 ℙℙ : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 ℙℙ X = ℙ (ℙ X)

 Space : 𝓤 ⁺ ⊔ 𝓥  ̇
 Space = Σ \(X : 𝓤 ̇ ) → Σ \(𝓞 : ℙℙ X) → axioms X 𝓞
\end{code}

If `(X , 𝓞X , a)` and `(Y , 𝓞Y , b)` are spaces, a
[homeomorphism](https://en.wikipedia.org/wiki/Homeomorphism) can be
described as a bijection `f : X → Y` such that the open sets of `Y`
are precisely those whose inverse images are open in `X`, which can be
written as

   > `(λ (V : ℙ Y) → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y`

Then `ι` defined below expresses the fact that a given bijection is a
homeomorphism:

\begin{code}
 sns-data : SNS ℙℙ (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ ℙℙ) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , 𝓞X) (Y , 𝓞Y) (f , _) = (λ (V : ℙ Y) → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y
\end{code}

What `ρ` says is that identity function is a homeomorphism, trivially:

\begin{code}
   ρ : (A : Σ ℙℙ) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , 𝓞) = refl 𝓞
\end{code}

Then `θ` amounts to the fact that two topologies on the same set must
be the same if they make the identity function into a homeomorphism.

\begin{code}
   h : {X : 𝓤 ̇ } {𝓞 𝓞' : ℙℙ X} → canonical-map ι ρ 𝓞 𝓞' ∼ 𝑖𝑑 (𝓞 ≡ 𝓞')
   h (refl 𝓞) = refl (refl 𝓞)

   θ : {X : 𝓤 ̇ } (𝓞 𝓞' : ℙℙ X) → is-equiv (canonical-map ι ρ 𝓞 𝓞')
   θ {X} 𝓞 𝓞' = equivs-closed-under-∼ (id-is-equiv (𝓞 ≡ 𝓞')) h
\end{code}

We introduce notation for the type of homeomorphisms:

\begin{code}
 _≅_  : Space → Space → 𝓤 ⊔ 𝓥 ̇

 (X , 𝓞X , _) ≅ (Y , 𝓞Y , _) =

              Σ \(f : X → Y) → is-equiv f
                             × ((λ V → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y)


 characterization-of-Space-≡ : is-univalent 𝓤
                             → (A B : Space)

                             → (A ≡ B) ≃ (A ≅ B)

 characterization-of-Space-≡ ua = characterization-of-≡-with-axioms ua
                                   sns-data axioms axiomss
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

But of course there are other choices for `R` that also make
sense. For example, we can take `R` to be a type of real numbers, with
the axioms for `X` and `F : (X → R) → R` saying that `F` is a linear
functional. Then the above gives a characterization of the identity
type of types equipped with linear functionals, in which case we may
prefer to rephrase the above as

\begin{code}
 _≅'_  : Space → Space → 𝓤 ⊔ 𝓥 ̇

 (X , F , _) ≅' (Y , G , _) =

             Σ \(f : X → Y) → is-equiv f
                            × ((λ (v : Y → R) → F (v ∘ f)) ≡ G)


 characterization-of-Space-≡' : is-univalent 𝓤
                              → (A B : Space)

                              → (A ≡ B) ≃ (A ≅' B)

 characterization-of-Space-≡' = characterization-of-Space-≡
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="selection-sip"></a> Selection spaces

\begin{code}
module selection-space-identity
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → X) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (ε : (X → R) → X) → is-subsingleton (axioms X ε))
       where

 open sip
 open sip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = (X → R) → X

 SelectionSpace : 𝓤 ⁺ ⊔ 𝓥  ̇
 SelectionSpace = Σ \(X : 𝓤 ̇ ) → Σ \(ε : S X) → axioms X ε

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , ε) (Y , δ) (f , _) = (λ (q : Y → R) → f (ε (q ∘ f))) ≡ δ

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , ε) = refl ε

   θ : {X : 𝓤 ̇ } (ε δ : S X) → is-equiv (canonical-map ι ρ ε δ)
   θ {X} ε δ = γ
    where
     h : canonical-map ι ρ ε δ ∼ 𝑖𝑑 (ε ≡ δ)
     h (refl ε) = refl (refl ε)

     γ : is-equiv (canonical-map ι ρ ε δ)
     γ = equivs-closed-under-∼ (id-is-equiv (ε ≡ δ)) h


 _≅_  :  SelectionSpace → SelectionSpace → 𝓤 ⊔ 𝓥 ̇

 (X , ε , _) ≅ (Y , δ , _) =

             Σ \(f : X → Y) → is-equiv f
                            × ((λ (q : Y → R) → f (ε (q ∘ f))) ≡ δ)


 characterization-of-selection-space-≡ : is-univalent 𝓤
                                       → (A B : SelectionSpace)

                                       → (A ≡ B) ≃ (A ≅ B)

 characterization-of-selection-space-≡ ua = characterization-of-≡-with-axioms ua
                                             sns-data
                                             axioms axiomss
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="contrived-sip"></a> A contrived example

Here is an example where we need to refer to the inverse of the
equivalence under consideration.

We take the opportunity to illustrate how the above boiler-plate code
can be avoided by defining `sns-data` on the fly, at the expense of
readability:

\begin{code}
module contrived-example-identity (𝓤 : Universe) where

 open sip

 contrived-≡ : is-univalent 𝓤 →

    (X Y : 𝓤 ̇ ) (φ : (X → X) → X) (γ : (Y → Y) → Y)
  →
    ((X , φ) ≡ (Y , γ)) ≃ Σ \(f : X → Y)
                        → Σ \(i : is-equiv f)
                        → (λ (g : Y → Y) → f (φ (inverse f i ∘ g ∘ f))) ≡ γ

 contrived-≡ ua X Y φ γ =
   characterization-of-≡ ua
    ((λ {(X , φ) (Y , γ) (f , i) → (λ (g : Y → Y) → f (φ (inverse f i ∘ g ∘ f))) ≡ γ}) ,
     (λ {(X , φ) → refl φ}) ,
     (λ {φ γ → equivs-closed-under-∼ (id-is-equiv (φ ≡ γ)) (λ {(refl φ) → refl (refl φ)})}))
    (X , φ) (Y , γ)
\end{code}

Many of the above examples can be written in such a concise form.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="functor-algebras-sip"></a> Functor algebras

In the following, we don't need to know that the functor preserves
composition or give coherence data for the identification `𝓕-id`.

\begin{code}
module generalized-functor-algebra-equality
         {𝓤 𝓥 : Universe}
         (F : 𝓤 ̇ → 𝓥 ̇ )
         (𝓕 : {X Y : 𝓤 ̇ } → (X → Y) → F X → F Y)
         (𝓕-id : {X : 𝓤 ̇ } → 𝓕 (𝑖𝑑 X) ≡ 𝑖𝑑 (F X))
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = F X → X

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , α) (Y , β) (f , _) = f ∘ α ≡ β ∘ 𝓕 f

   ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , α) = α        ≡⟨ ap (α ∘_) (𝓕-id ⁻¹) ⟩
               α ∘ 𝓕 id ∎

   θ : {X : 𝓤 ̇ } (α β : S X) → is-equiv (canonical-map ι ρ α β)
   θ {X} α β = γ
    where
     c : α ≡ β → α ≡ β ∘ 𝓕 id
     c = transport (α ≡_) (ρ (X , β))

     i : is-equiv c
     i = transport-is-equiv (α ≡_) (ρ (X , β))

     h : canonical-map ι ρ α β ∼ c
     h (refl _) = ρ (X , α)          ≡⟨ refl-left ⁻¹ ⟩
                  refl α ∙ ρ (X , α) ∎

     γ : is-equiv (canonical-map ι ρ α β)
     γ = equivs-closed-under-∼ i h


 characterization-of-functor-algebra-≡ : is-univalent 𝓤 →

     (X Y : 𝓤 ̇ ) (α : F X → X) (β : F Y → Y)
   →
     ((X , α) ≡ (Y , β))  ≃  Σ \(f : X → Y) → is-equiv f × (f ∘ α ≡ β ∘ 𝓕 f)

 characterization-of-functor-algebra-≡ ua X Y α β =
   characterization-of-≡ ua sns-data (X , α) (Y , β)
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity equivalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="infty-preorders-sip"></a> Type-valued preorders

This example is harder than the previous ones.

A type-valued preorder on a type `X` is a type-valued relation which
is reflexive and transitive. A type-valued, as opposed to a
subsingleton-valued, preorder could also be called an
∞-preorder.

\begin{code}
type-valued-preorder-S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
type-valued-preorder-S {𝓤} {𝓥} X = Σ \(_≤_ : X → X → 𝓥 ̇ )
                                 → ((x : X) → x ≤ x)
                                 × ((x y z : X) → x ≤ y → y ≤ z → x ≤ z)
\end{code}

A [category](HoTT-UF-Agda.html#categories-sip), also known as a
`1`-category, is a type-valued preorder subject to suitable axioms,
where the relation `_≤_` is traditionally written `hom`, and where
identities are given by the reflexivity law, and composition is given
by the transitivity law.

We choose to use categorical notation and terminology for type-valued
preorders.

\begin{code}
module type-valued-preorder-identity
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
       where

 open sip

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}

 Type-valued-preorder : (𝓤 ⊔ 𝓥) ⁺ ̇
 Type-valued-preorder = Σ S
\end{code}

But we will use the shorter notation `Σ S` in this submodule.

The type of objects of a type-valued preorder:

\begin{code}
 Ob : Σ S → 𝓤 ̇
 Ob (X , homX , idX , compX ) = X
\end{code}

Its hom-types (or preorder):

\begin{code}
 hom : (𝓧 : Σ S) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , homX , idX , compX) = homX
\end{code}

Its identities (or reflexivities):

\begin{code}
 𝒾𝒹 : (𝓧 : Σ S) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , homX , idX , compX) = idX
\end{code}

Its composition law (or transitivity):

\begin{code}
 comp : (𝓧 : Σ S) (x y z : Ob 𝓧) → hom 𝓧 x y → hom 𝓧 y z → hom 𝓧 x z
 comp (X , homX , idX , compX) = compX
\end{code}

Notice that we have the so-called *diagramatic order* for
composition.

The functoriality of a pair `F , 𝓕` (where in category theory the
latter is also written `F`, by an [abuse of
notation](https://en.wikipedia.org/wiki/Abuse_of_notation)) says that
`𝓕` preserves identities and composition:

\begin{code}
 functorial : (𝓧 𝓐 : Σ S)
            → (F : Ob 𝓧 → Ob 𝓐)
            → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            → 𝓤 ⊔ 𝓥 ̇

 functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where
\end{code}

In order to express the preservation of identities and composition in
traditional form, we first define, locally, symbols for composition
in applicative order, making the objects implicit:

\begin{code}
   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g
\end{code}

And we also make implicit the object parameters of the action of the
functor on arrows:

\begin{code}
   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f
\end{code}

Preservation of identities:

\begin{code}
   pidentity = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ≡ (λ x → 𝒾𝒹 𝓐 (F x))
\end{code}

Preservation of composition:

\begin{code}
   pcomposition = (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
                ≡ (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)
\end{code}

This time we will need two steps to characterize equality of
type-valued preorders. The first one is as above, by considering a
standard notion of structure:

\begin{code}
 sns-data : SNS S (𝓤 ⊔ (𝓥 ⁺))
 sns-data = (ι , ρ , θ)
  where
   ι : (𝓧 𝓐 : Σ S) → ⟨ 𝓧 ⟩ ≃ ⟨ 𝓐 ⟩ → 𝓤 ⊔ (𝓥 ⁺) ̇
   ι 𝓧 𝓐 (F , _) = Σ \(p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
                         → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)

   ρ : (𝓧 : Σ S) → ι 𝓧 𝓧 (id-≃ ⟨ 𝓧 ⟩)
   ρ 𝓧 = refl (hom 𝓧) , refl (𝒾𝒹 𝓧) , refl (comp 𝓧)

   θ : {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)
   θ {X} (homX , idX , compX) (homA , idA , compA) = g
    where
     φ = canonical-map ι ρ (homX , idX , compX) (homA , idA , compA)

     γ : codomain φ → domain φ
     γ (refl _ , refl _ , refl _) = refl _

     η : γ ∘ φ ∼ id
     η (refl _) = refl _

     ε : φ ∘ γ ∼ id
     ε (refl _ , refl _ , refl _) = refl _

     g : is-equiv φ
     g = invertibles-are-equivs φ (γ , η , ε)
\end{code}

The above constructions are short thanks to
computations-under-the-hood performed by Agda, and may require some
effort to unravel.

The above automatically gives a characterization of equality of
preorders. But this characterization uses another equality, of hom
types. The second step translates this equality into an equivalence:

\begin{code}
 lemma : (𝓧 𝓐 : Σ S) (F : Ob 𝓧 → Ob 𝓐)
       →
         (Σ \(p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
                → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p))
       ≃
          Σ \(𝓕 : (x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                → (∀ x y → is-equiv (𝓕 x y))
                × functorial 𝓧 𝓐 F 𝓕

 lemma 𝓧 𝓐 F = γ
  where
   e = (hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))                                         ≃⟨ i   ⟩
       (∀ x y → hom 𝓧 x y ≡ hom 𝓐 (F x) (F y))                                     ≃⟨ ii  ⟩
       (∀ x y → hom 𝓧 x y ≃ hom 𝓐 (F x) (F y))                                     ≃⟨ iii ⟩
       (∀ x → Σ \(φ : ∀ y → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                    → ∀ y → is-equiv (φ y))                                        ≃⟨ iv  ⟩
       (Σ \(𝓕 : (x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
              → (∀ x y → is-equiv (𝓕 x y)))                                        ■
    where
     i   = hfunext₂-≃ hfe hfe (hom 𝓧 )  λ x y → hom 𝓐 (F x) (F y)
     ii  = Π-cong fe fe
            (λ x → Π-cong fe fe
            (λ y → univalence-≃ (ua 𝓥) (hom 𝓧 x y) (hom 𝓐 (F x) (F y))))
     iii = Π-cong fe fe (λ y → ΠΣ-distr-≃)
     iv  = ΠΣ-distr-≃
\end{code}

Here Agda silently performs a laborious computation to accept the
definition of item `v`:

\begin{code}
   v : (p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
     → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)
     ≃ functorial 𝓧 𝓐 F (pr₁ (Eq→fun e p))

   v (refl _) = id-≃ _

   γ =

    (Σ \(p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
           → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p))   ≃⟨ vi   ⟩

    (Σ \(p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
           → functorial 𝓧 𝓐 F (pr₁ (Eq→fun e p)))                    ≃⟨ vii  ⟩

    (Σ \(σ : Σ \(𝓕 : (x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                   → (∀ x y → is-equiv (𝓕 x y)))
           → functorial 𝓧 𝓐 F (pr₁ σ))                               ≃⟨ viii ⟩

    (Σ \(𝓕 : (x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                  → (∀ x y → is-equiv (𝓕 x y))
                  × functorial 𝓧 𝓐 F 𝓕)                              ■
    where
     vi   = Σ-cong v
     vii  = ≃-sym (Σ-change-of-variable _ (Eq→fun e) (Eq→fun-is-equiv e))
     viii = Σ-assoc
\end{code}

Combining the two steps, we get the following characterization of
equality of type-valued preorders in terms of equivalences:

\begin{code}
 characterization-of-type-valued-preorder-≡ :

      (𝓧 𝓐 : Σ S)
    →
      (𝓧 ≡ 𝓐)
    ≃
      Σ \(F : Ob 𝓧 → Ob 𝓐)
            → is-equiv F
            × Σ \(𝓕 : (x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                    → (∀ x y → is-equiv (𝓕 x y))
                    × functorial 𝓧 𝓐 F 𝓕

 characterization-of-type-valued-preorder-≡ 𝓧 𝓐 =

   (𝓧 ≡ 𝓐)                                                                ≃⟨ i  ⟩
   (Σ \(F : Ob 𝓧 → Ob 𝓐)
          → is-equiv F
          × Σ \(p : hom 𝓧 ≡ λ x y → hom 𝓐 (F x) (F y))
                  → functorial 𝓧 𝓐 F (λ x y → transport (λ - → - x y) p)) ≃⟨ ii ⟩
   _                                                                      ■

  where
   i  = characterization-of-≡ (ua 𝓤) sns-data 𝓧 𝓐
   ii = Σ-cong (λ F → Σ-cong (λ _ → lemma 𝓧 𝓐 F))
\end{code}

*Exercise*. The above equivalence is characterized by induction on
identifications as the function that maps the reflexive identification
to the identity functor.

Now we consider type-valued preorders subject to arbitrary axioms. The
only reason we need to consider this explicitly is that again we need
to combine two steps. The second step is the same, but the first step
is modified to add axioms.

\begin{code}
module type-valued-preorder-with-axioms-identity
        (𝓤 𝓥 𝓦 : Universe)
        (ua : Univalence)
        (axioms  : (X : 𝓤 ̇ ) → type-valued-preorder-S {𝓤} {𝓥} X → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (s : type-valued-preorder-S X) → is-subsingleton (axioms X s))
       where

 open sip
 open sip-with-axioms
 open type-valued-preorder-identity 𝓤 𝓥 ua

 S' : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ̇
 S' X = Σ \(s : S X) → axioms X s

 sns-data' : SNS S' (𝓤 ⊔ (𝓥 ⁺))
 sns-data' = add-axioms axioms axiomss sns-data
\end{code}

Recall that `[_]` is the map that forgets the axioms.

\begin{code}
 characterization-of-type-valued-preorder-≡-with-axioms :

      (𝓧' 𝓐' : Σ S')
    →
      (𝓧' ≡ 𝓐')
    ≃
      Σ \(F : Ob [ 𝓧' ] → Ob [ 𝓐' ])
            → is-equiv F
            × Σ \(𝓕 : (x y : Ob [ 𝓧' ]) → hom [ 𝓧' ] x y → hom [ 𝓐' ] (F x) (F y))
                    → (∀ x y → is-equiv (𝓕 x y))
                    × functorial [ 𝓧' ] [ 𝓐' ] F 𝓕

 characterization-of-type-valued-preorder-≡-with-axioms 𝓧' 𝓐' =

  (𝓧' ≡ 𝓐')                     ≃⟨ i  ⟩
  ([ 𝓧' ] ≃[ sns-data ] [ 𝓐' ]) ≃⟨ ii ⟩
  _                              ■

  where
   i  = characterization-of-≡-with-axioms (ua 𝓤) sns-data axioms axiomss 𝓧' 𝓐'
   ii = Σ-cong (λ F → Σ-cong (λ _ → lemma [ 𝓧' ] [ 𝓐' ] F))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="categories-sip"></a> Categories

By choosing suitable axioms for type-valued preorders, we get categories:

\begin{code}
module category-identity
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
       where

 open type-valued-preorder-with-axioms-identity 𝓤 𝓥 (𝓤 ⊔ 𝓥) ua

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}
\end{code}

The axioms say that

  1. the homs form sets, rather than arbitrary types,
  2. the identity is a left and right neutral element of composition,
  3. composition is associative.

\begin{code}
 category-axioms : (X : 𝓤 ̇ ) → S X → 𝓤 ⊔ 𝓥 ̇
 category-axioms X (homX , idX , compX) = hom-sets × identityl × identityr × associativity
  where
   _o_ : {x y z : X} → homX y z → homX x y → homX x z
   g o f = compX _ _ _ f g

   hom-sets      = ∀ x y → is-set (homX x y)

   identityl     = ∀ x y (f : homX x y) → f o (idX x) ≡ f

   identityr     = ∀ x y (f : homX x y) → (idX y) o f ≡ f

   associativity = ∀ x y z t (f : homX x y) (g : homX y z) (h : homX z t)
                 → (h o g) o f ≡ h o (g o f)
\end{code}

The first axiom is subsingleton valued because the property of being a
set is a subsingleton type. The second and the third axioms are
subsingleton valued in the presence of the first axiom, because
equations between elements of sets are subsingletons, by definition of
set. And because subsingletons are closed under products, the category
axioms form a subsingleton type:

\begin{code}
 category-axioms-subsingleton : (X : 𝓤 ̇ ) (s : S X) → is-subsingleton (category-axioms X s)
 category-axioms-subsingleton X (homX , idX , compX) ca = γ ca
  where
   i : ∀ x y → is-set (homX x y)
   i = pr₁ ca

   γ : is-subsingleton (category-axioms X (homX , idX , compX))
   γ = ×-is-subsingleton ss (×-is-subsingleton ls (×-is-subsingleton rs as))
    where
     ss = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → being-set-is-subsingleton fe))

     ls = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → Π-is-subsingleton fe
           (λ f → i x y (compX x x y (idX x) f) f)))

     rs = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → Π-is-subsingleton fe
           (λ f → i x y (compX x y y f (idX y)) f)))

     as = Π-is-subsingleton fe
           (λ x → Π-is-subsingleton fe
           (λ y → Π-is-subsingleton fe
           (λ z → Π-is-subsingleton fe
           (λ t → Π-is-subsingleton fe
           (λ f → Π-is-subsingleton fe
           (λ g → Π-is-subsingleton fe
           (λ h → i x t (compX x y t f (compX y z t g h))
                        (compX x z t (compX x y z f g) h))))))))
\end{code}

We are now ready to define the type of categories, as a subtype of
that of type-valued preorders:

\begin{code}
 Cat : (𝓤 ⊔ 𝓥)⁺ ̇
 Cat = Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → category-axioms X s
\end{code}

We reuse of above names in a slightly different way, taking into
account that now we have axioms, which we simply ignore:

\begin{code}
 Ob : Cat → 𝓤 ̇
 Ob (X , (homX , idX , compX) , _) = X

 hom : (𝓧 : Cat) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , (homX , idX , compX) , _) = homX


 𝒾𝒹 : (𝓧 : Cat) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , (homX , idX , compX) , _) = idX

 comp : (𝓧 : Cat) (x y z : Ob 𝓧) (f : hom 𝓧 x y) (g : hom 𝓧 y z) → hom 𝓧 x z
 comp (X , (homX , idX , compX) , _) = compX


 is-functorial : (𝓧 𝓐 : Cat)
               → (F : Ob 𝓧 → Ob 𝓐)
               → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
               → 𝓤 ⊔ 𝓥 ̇

 is-functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where
   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g

   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f

   pidentity    = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ≡ (λ x → 𝒾𝒹 𝓐 (F x))

   pcomposition = (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
                ≡ (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)
\end{code}

*Exercise*. For type-valued preorders, `functorial 𝓧 𝓐 F 𝓕` is not in
 general a subsingleton, but for categories, `is-functorial 𝓧 𝓐 F 𝓕`
 is always a subsingleton.

We now apply the module `type-valued-preorder-with-axioms-identity` to
get the following characterization of identity of categories:

\begin{code}
 _⋍_ : Cat → Cat → 𝓤 ⊔ 𝓥 ̇

 𝓧 ⋍ 𝓐 = Σ \(F : Ob 𝓧 → Ob 𝓐)
               → is-equiv F
               × Σ \(𝓕 : (x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
                       → (∀ x y → is-equiv (𝓕 x y))
                       × is-functorial 𝓧 𝓐 F 𝓕


 Id→EqCat : (𝓧 𝓐 : Cat) → 𝓧 ≡ 𝓐 → 𝓧 ⋍ 𝓐
 Id→EqCat 𝓧 𝓧 (refl 𝓧) = 𝑖𝑑 (Ob 𝓧 ) ,
                         id-is-equiv (Ob 𝓧 ) ,
                         (λ x y → 𝑖𝑑 (hom 𝓧 x y)) ,
                         (λ x y → id-is-equiv (hom 𝓧 x y)) ,
                         refl (𝒾𝒹 𝓧) ,
                         refl (comp 𝓧)


 characterization-of-category-≡ : (𝓧 𝓐 : Cat) → (𝓧 ≡ 𝓐) ≃ (𝓧 ⋍ 𝓐)
 characterization-of-category-≡ = characterization-of-type-valued-preorder-≡-with-axioms
                                   category-axioms category-axioms-subsingleton


 Id→EqCat-is-equiv : (𝓧 𝓐 : Cat) → is-equiv (Id→EqCat 𝓧 𝓐)
 Id→EqCat-is-equiv 𝓧 𝓐 = equivs-closed-under-∼
                           (Eq→fun-is-equiv (characterization-of-category-≡ 𝓧 𝓐))
                           (γ 𝓧 𝓐)
  where
   γ : (𝓧 𝓐 : Cat) → Id→EqCat 𝓧 𝓐 ∼ Eq→fun (characterization-of-category-≡ 𝓧 𝓐)
   γ 𝓧 𝓧 (refl 𝓧) = refl _
\end{code}

The HoTT book has a characterization of identity of categories as
equivalence of categories in the traditional sense of category theory,
assuming that the categories are univalent in a certain sense. We have
chosen not to include the univalence requirement in our notion of
category, although it may be argued that *univalent category* is the
correct notion of category for univalent mathematics (because a
univalent category may be equivalently defined as a category object in
a 1-groupoid). In any case, the characterization of equality given
here is not affected by the univalence requirement, or any
subsingleton-valued property of categories.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="truncation"></a> Subsingleton truncation

#### <a id="vvaproach"> Voevodsky's approach to subsingleton truncation

The following is Voevosky's approach to saying that a type is
inhabited in such a way that the statement of inhabitation is a
subsingleton, using relying on function extensionality.

\begin{code}
is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P
\end{code}

This says that if we have a function from `X` to a subsingleton `P`, then
`P` must have a point. So this fails when `X=𝟘`. Considering `P=𝟘`, we conclude
that `¬¬ X` if `X` is inhabited, which says that `X` is non-empty.

For simplicity in the formulation of the theorems, we assume *global*
function extensionality.
A type can be pointed in many ways, but inhabited in at most one way:

\begin{code}
inhabitation-is-subsingleton : global-dfunext → (X : 𝓤 ̇ )
                             → is-subsingleton (is-inhabited X)

inhabitation-is-subsingleton fe X =
 Π-is-subsingleton fe
   (λ P → Π-is-subsingleton fe
   (λ (s : is-subsingleton P) → Π-is-subsingleton fe
   (λ (f : X → P) → s)))

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
  φ x = transport P (inhabitation-is-subsingleton fe X (pointed-is-inhabited x) s)
                    (f x)
  φ' : is-inhabited X → P s
  φ' = inhabited-recursion X (P s) (i s) φ


inhabited-computation : (fe : global-dfunext) {X : 𝓤 ̇ } {P : is-inhabited X → 𝓤 ̇ }
                      → (i : (s : is-inhabited X) → is-subsingleton (P s))
                      → (f : (x : X) → P (pointed-is-inhabited x))
                      → (x : X)
                      → inhabited-induction fe i f (pointed-is-inhabited x) ≡ f x

inhabited-computation fe i f x = i (pointed-is-inhabited x)
                                   (inhabited-induction fe i f
                                     (pointed-is-inhabited x))
                                   (f x)
\end{code}

The definition of inhabitation looks superficially like double negation.
However, although we [don't necessarily have](HoTT-UF-Agda.html#moreexercises) that
`¬¬ P → P`, we do have that `is-inhabited P → P` if `P` is a subsingleton.

\begin{code}
inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ )
                                          → is-subsingleton P → is-inhabited P → P

inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s (𝑖𝑑 P)
\end{code}

*Exercise*. [Show](https://lmcs.episciences.org/3217) that
 `is-inhabited X ⇔ ¬¬X` if and only if excluded middle holds.

\begin{code}
inhabited-functorial : global-dfunext → (X : 𝓤 ⁺ ̇ ) (Y : 𝓤 ̇ )
                     → (X → Y) → is-inhabited X → is-inhabited Y

inhabited-functorial fe X Y f = inhabited-recursion
                                  X
                                  (is-inhabited Y)
                                  (inhabitation-is-subsingleton fe Y)
                                  (pointed-is-inhabited ∘ f)
\end{code}

This universe assignment for functoriality is fairly restrictive, but
is the only possible one.

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

*Exercise*. The type
`(y : codomain f) → Σ \(x : domain f) → f x ≡ y` [is equivalent
 to](HoTT-UF-Agda.html#has-section-charac) the type `has-section f`,
 which is stronger than saying that `f` is a surjection.

There are two problems with this definition of inhabitation:

  * Inhabitation has values in the next universe.

  * We can eliminate into subsingletons of the same universe only.

In particular, it is not possible to show that the map `X →
is-inhabited X` is a surjection, or that `X → Y` gives `is-inhabited X
→ is-inhabited Y` for `X` and `Y` in arbitrary universes.

There are two proposed ways to solve this kind of problem:

  1. Voevodsky works with certain [resizing
     rules](http://www.math.ias.edu/vladimir/files/2011_Bergen.pdf)
     for subsingletons. At the time of writing, the (relative)
     consistency of the system with such rules is an open question.

  2. The HoTT book works with certain higher inductive types (HIT's),
     which are known to have models and hence to be (relatively)
     consistent.  This is the same approach adopted by cubical type
     theory and cubical Agda.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="axiomatic-approach"> An axiomatic approach

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
  ∥∥-is-subsingleton   : {𝓤 : Universe} {X : 𝓤 ̇ } → is-subsingleton ∥ X ∥
  ∣_∣                  : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-recursion         : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                       → is-subsingleton P → (X → P) → ∥ X ∥ → P
\end{code}

This is the approach we adopt in our [personal Agda
development](https://www.cs.bham.ac.uk/~mhe/agda-new/).

We now assume that subsingleton truncations exist in the next few
constructions, and we `open` the assumption to make the above fields
visible.

\begin{code}
module basic-truncation-development
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

  open subsingleton-truncations-exist pt public

  hunapply : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g
  hunapply = hfunext-gives-dfunext hfe


  ∥∥-induction : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
              → ((s : ∥ X ∥) → is-subsingleton (P s))
              → ((x : X) → P ∣ x ∣)
              → (s : ∥ X ∥) → P s

  ∥∥-induction {𝓤} {𝓥} {X} {P} i f s = φ' s
   where
    φ : X → P s
    φ x = transport P (∥∥-is-subsingleton ∣ x ∣ s) (f x)
    φ' : ∥ X ∥ → P s
    φ' = ∥∥-recursion (i s) φ


  ∥∥-computation : {X : 𝓤 ̇ } {P : ∥ X ∥ → 𝓥 ̇ }
                 → (i : (s : ∥ X ∥) → is-subsingleton (P s))
                 → (f : (x : X) → P ∣ x ∣)
                 → (x : X)
                 → ∥∥-induction i f ∣ x ∣ ≡ f x

  ∥∥-computation i f x = i ∣ x ∣ (∥∥-induction i f ∣ x ∣) (f x)


  ∥∥-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥ → ∥ Y ∥
  ∥∥-functor f = ∥∥-recursion ∥∥-is-subsingleton (λ x → ∣ f x ∣)
\end{code}

The subsingleton truncation of a type and its inhabitation are
logically equivalent propositions:

\begin{code}
  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇ ) → ∥ X ∥ ⇔ is-inhabited X
  ∥∥-agrees-with-inhabitation X = a , b
   where
    a : ∥ X ∥ → is-inhabited X
    a = ∥∥-recursion (inhabitation-is-subsingleton hunapply X) pointed-is-inhabited

    b : is-inhabited X → ∥ X ∥
    b = inhabited-recursion X ∥ X ∥ ∥∥-is-subsingleton ∣_∣
\end{code}

Hence they differ only in size, and when size matters don't get on the
way, we can use `is-inhabited` instead of `∥_∥` if we wish.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="disjunction-and-existence"> Disjunction and existence

Disjunction and existence are defined as the truncation of `+` and `Σ`:

\begin{code}
  _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ∨ B = ∥ A + B ∥

  infixl 20 _∨_

  ∃ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃ A = ∥ Σ A ∥

  ∨-is-subsingleton : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → is-subsingleton (A ∨ B)
  ∨-is-subsingleton = ∥∥-is-subsingleton

  ∃-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → is-subsingleton (∃ A)
  ∃-is-subsingleton = ∥∥-is-subsingleton

\end{code}

The author's slides on [univalent
logic](https://www.newton.ac.uk/seminar/20170711100011001) discuss
further details about these notions of disjunction and existence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="images-and-surjections"> Images and surjections

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


  being-surjection-is-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → is-subsingleton (is-surjection f)

  being-surjection-is-subsingleton f = Π-is-subsingleton hunapply
                                        (λ y → ∃-is-subsingleton)


  corestriction-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                           → is-surjection (corestriction f)

  corestriction-surjection f (y , s) = ∥∥-functor g s
   where
    g : (Σ \x → f x ≡ y) → Σ \x → corestriction f x ≡ y , s
    g (x , p) = x , to-Σ-≡ (p , ∥∥-is-subsingleton _ _)


  surjection-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → is-surjection f
                       → (P : Y → 𝓦 ̇ )
                       → ((y : Y) → is-subsingleton (P y))
                       → ((x : X) → P (f x))
                       → (y : Y) → P y
  surjection-induction f i P j α y = ∥∥-recursion (j y) φ (i y)
   where
    φ : (σ : fiber f y) → P y
    φ (x , r) = transport P r (α x)
\end{code}

*Exercise*. A map is an equivalence if and only if it is
 both an embedding and a surjection. (To be solved shortly.)

This time we can prove that the map `x ↦ ∣ x ∣` of `X` into `∥ X ∥` is
a surjection without the universe levels getting in our way:

\begin{code}
  ∣∣-is-surjection : (X : 𝓤 ̇ ) → is-surjection (λ (x : X) → ∣ x ∣)
  ∣∣-is-surjection X s = γ
   where
    f : X → ∃ \(x : X) → ∣ x ∣ ≡ s
    f x = ∣ (x , ∥∥-is-subsingleton ∣ x ∣ s) ∣

    γ : ∃ \(x : X) → ∣ x ∣ ≡ s
    γ = ∥∥-recursion ∥∥-is-subsingleton f s
\end{code}

Saying that this surjection `X → ∥ X ∥` has a section for all `X` (we
can pick a point of every inhabited type) amounts to [global
choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice), which
[contradicts univalence](https://homotopytypetheory.org/book/), and
also [gives classical logic](https://lmcs.episciences.org/3217).

*Exercise* (hard). If `X` and `Y` are types obtained by summing `x-` and
  `y`-many copies of the type `𝟙`, respectively, as in `𝟙 + 𝟙 + ... + 𝟙` , where `x`
  and `y` are natural numbers, then `∥ X ≡ Y ∥ ≃ (x ≡ y)` and the type
  `X ≡ X` has `x!` elements.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="equivalence-characterization"> A characterization of equivalences


Singletons are inhabited, of course:

\begin{code}
  singletons-are-inhabited : (X : 𝓤 ̇ )
                           → is-singleton X
                           → ∥ X ∥

  singletons-are-inhabited X s = ∣ center X s ∣
\end{code}

And inhabited subsingletons are singletons:

\begin{code}
  inhabited-subsingletons-are-singletons : (X : 𝓤 ̇ )
                                         → ∥ X ∥
                                         → is-subsingleton X
                                         → is-singleton X

  inhabited-subsingletons-are-singletons X t i = c , φ
   where
    c : X
    c = ∥∥-recursion i (𝑖𝑑 X) t

    φ : (x : X) → c ≡ x
    φ = i c
\end{code}

Hence a type is a singleton if and only if it is inhabited and a
subsingleton:

\begin{code}
  singleton-iff-inhabited-subsingleton : (X : 𝓤 ̇ )
                                       → is-singleton X
                                       ⇔ (∥ X ∥ × is-subsingleton X)

  singleton-iff-inhabited-subsingleton X =
    (λ (s : is-singleton X) → singletons-are-inhabited     X s ,
                              singletons-are-subsingletons X s) ,
    Σ-induction (inhabited-subsingletons-are-singletons X)
\end{code}

By considering the unique map `X → 𝟙`, this can be regarded as a
particular case of the fact that a map is an equivalence if and only
if it is both an embedding and a surjection:

\begin{code}
  equiv-iff-embedding-and-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     →  is-equiv f
                                     ⇔ (is-embedding f × is-surjection f)

  equiv-iff-embedding-and-surjection f = (a , b)
   where
    a : is-equiv f → is-embedding f × is-surjection f
    a e = (λ y → singletons-are-subsingletons (fiber f y) (e y)) ,
          (λ y → singletons-are-inhabited     (fiber f y) (e y))

    b : is-embedding f × is-surjection f → is-equiv f
    b (e , s) y = inhabited-subsingletons-are-singletons (fiber f y) (s y) (e y)


  equiv-≡-embedding-and-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                   → propext (𝓤 ⊔ 𝓥)
                                   →  is-equiv f
                                   ≡ (is-embedding f × is-surjection f)

  equiv-≡-embedding-and-surjection f pe =
    pe (being-equiv-is-subsingleton hunapply hunapply f)
       (×-is-subsingleton
         (being-embedding-is-subsingleton hunapply f)
         (being-surjection-is-subsingleton f))
       (lr-implication (equiv-iff-embedding-and-surjection f))
       (rl-implication (equiv-iff-embedding-and-surjection f))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="exiting-truncations"></a> Exiting subsingleton truncations

We will see that [global choice](HoTT-UF-Agda.html#global-choice)

   > (X : 𝓤 ̇ ) → `∥ X ∥ → X`

is inconsistent with univalence, and also implies excluded
middle. However, for some types `X`, we can exit the truncation, which
is what we show in this section.

Because, as we have seen, we have a logical equivalence

   > `∥ X ∥ ⇔ is-inhabited X`,

it suffices to consider

   > `is-inhabited X → X`,

which can be done in our spartan MLTT without any axioms for univalent mathematics (hence hence with axioms for univalent mathematics, including classical ones such as excluded middle and (non-global) choice).

For any type `X`, we have `is-inhabited X → X`
[iff](https://lmcs.episciences.org/3217/) `X` has a designated
[wconstant-endomap](HoTT-UF-Agda.html#wconstant-endomap). To prove this we first
show that the type of fixed points of a `wconstant` endomap is a
subsingleton.

The type of fixed points of an endomap:

\begin{code}
fix : {X : 𝓤 ̇ } → (X → X) → 𝓤 ̇
fix f = Σ \(x : domain f) → f x ≡ x

from-fix : {X : 𝓤 ̇ } (f : X → X)
         → fix f → X
from-fix f = pr₁
\end{code}

Conversely, if `f` is `wconstant` then for any `x : X` we have that `f
x` is a fixed point of `f`:

\begin{code}
to-fix : {X : 𝓤 ̇ } (f : X → X) → wconstant f
       → X → fix f
to-fix f κ x = f x , κ (f x) x
\end{code}

The following is trivial if the type `X` is a set. What may be
surprising is that it holds for arbitrary types, because in this case the type `f x ≡ x` is in general not a subsingleton (consider e.g. `X = 𝓤₀ ̇ ` and `f = λ _ → 𝟚`).

\begin{code}
fix-is-subsingleton : {X : 𝓤 ̇ } (f : X → X)
                    → wconstant f → is-subsingleton (fix f)

fix-is-subsingleton {𝓤} {X} f κ = γ
 where
  a : (y x : X) → (f x ≡ x) ≃ (f y ≡ x)
  a y x = transport (_≡ x) (κ x y) , transport-is-equiv (_≡ x) (κ x y)

  b : (y : X) → fix f ≃ singleton-type' (f y)
  b y = Σ-cong (a y)

  c : X → is-singleton (fix f)
  c y = equiv-to-singleton (b y) (singleton-types'-are-singletons X (f y))

  d : fix f → is-singleton (fix f)
  d = c ∘ from-fix f

  γ : is-subsingleton (fix f)
  γ = subsingleton-criterion d
\end{code}

*Exercise.* Formulate and prove the fact that the type `fix f` has the
 universal property of the subsingleton truncation of `X` if `f` is
 `wconstant`. Moreover, argue that the computation rule holds
 definitionally in this case. This is an example of a situation when
 the truncation of a type just is available in MLTT without axioms or
 extensions.

We use `fix-is-subsingleton` to show that the type `is-inhabited X →
X` is logically equivalent to the type `wconstant-endomap X`, where
one direction uses function extensionality. We refer to a function
`is-inhabited X → X` as a *choice function* for `X`. So a type has a
choice function if and only if it has a designated `wconstant`
endomap.

\begin{code}
choice-function : 𝓤 ̇ → 𝓤 ⁺ ̇
choice-function X = is-inhabited X → X
\end{code}

With a constant endomap of `X`, we can exit the truncation
`is-inhabited X` in pure MLTT:

\begin{code}
wconstant-endomap-gives-choice-function : {X : 𝓤 ̇ }
                                        → wconstant-endomap X → choice-function X
wconstant-endomap-gives-choice-function {𝓤} {X} (f , κ) = from-fix f ∘ γ
 where
  γ : is-inhabited X → fix f
  γ = inhabited-recursion X (fix f) (fix-is-subsingleton f κ) (to-fix f κ)
\end{code}

For the converse we use function extensionality (to know that
`is-inhabited X` is a subsingleton in the construction of the `wconstant`
endomap):

\begin{code}
choice-function-gives-wconstant-endomap : global-dfunext
                                        → {X : 𝓤 ̇ }
                                        → choice-function X → wconstant-endomap X
choice-function-gives-wconstant-endomap fe {X} c = f , κ
 where
  f : X → X
  f = c ∘ pointed-is-inhabited

  κ : wconstant f
  κ x y = ap c (inhabitation-is-subsingleton fe X (pointed-is-inhabited x)
               (pointed-is-inhabited y))
\end{code}

As an application, we show that if the type of roots of a function `f
: ℕ → ℕ` is inhabited, then it is pointed. In other words, with the
information that there is some root, then we can find an explicit root.

\begin{code}
module find-hidden-root where

 open basic-arithmetic-and-order public
\end{code}

Given a root, we find a minimal root (below it, of course) by bounded
search, and this gives a constant endomap of the type of roots:

\begin{code}
 μρ : (f : ℕ → ℕ) → root f → root f
 μρ f (n , p) = minimal-root-is-root f (bounded-search-ℕ-minimal-root f n p)

 μρ-root : (f : ℕ → ℕ) → root f → ℕ
 μρ-root f r = pr₁ (μρ f r)

 μρ-root-is-root : (f : ℕ → ℕ) (r : root f) → f (μρ-root f r) ≡ 0
 μρ-root-is-root f r = pr₂ (μρ f r)

 μρ-root-minimal : (f : ℕ → ℕ) (m : ℕ) (p : f m ≡ 0)
                 → (n : ℕ) → f n ≡ 0 → μρ-root f (m , p) ≤ n
 μρ-root-minimal f m p n q = not-less-bigger-or-equal
                              (μρ-root f (m , p)) n (φ (dni (f n ≡ 0) q))
  where
   φ : ¬(f n ≢ 0) → ¬(n < μρ-root f (m , p))
   φ = contrapositive (pr₂(pr₂ (bounded-search-ℕ-minimal-root f m p)) n)
\end{code}

The crucial property of the function `μρ` is that it is `wconstant`:

\begin{code}
 μρ-wconstant : (f : ℕ → ℕ) → wconstant (μρ f)
 μρ-wconstant f (n , p) (n' , p') = r
  where
   m m' : ℕ
   m  = μρ-root f (n , p)
   m' = μρ-root f (n' , p')

   l : m ≤ m'
   l = μρ-root-minimal f n p m' (μρ-root-is-root f (n' , p'))

   l' : m' ≤ m
   l' = μρ-root-minimal f n' p' m (μρ-root-is-root f (n , p))

   q : m ≡ m'
   q = ≤-anti _ _ l l'

   r : μρ f (n , p) ≡ μρ f (n' , p')
   r = to-Σ-≡ (q , ℕ-is-set _ _ _ _)
\end{code}

Using the `wconstancy` of `μρ`, if a root of `f` exists, then we can
find one (which in fact will be the minimal one):

\begin{code}
 find-existing-root : (f : ℕ → ℕ) → is-inhabited (root f) → root f
 find-existing-root f = h ∘ g
   where
    γ : root f → fix (μρ f)
    γ = to-fix (μρ f) (μρ-wconstant f)

    g : is-inhabited (root f) → fix (μρ f)
    g = inhabited-recursion (root f) (fix (μρ f))
         (fix-is-subsingleton (μρ f) (μρ-wconstant f)) γ

    h : fix (μρ f) → Σ \(n : ℕ) → f n ≡ 0
    h = from-fix (μρ f)
\end{code}

In the following example, we first hide a root with
`pointed-is-inhabited` and then find the minimal root with search
bounded by this hidden root:

\begin{code}
 module find-existing-root-example where

  f : ℕ → ℕ
  f 0 = 1
  f 1 = 1
  f 2 = 0
  f 3 = 1
  f 4 = 0
  f 5 = 1
  f 6 = 1
  f 7 = 0
  f (succ (succ (succ (succ (succ (succ (succ (succ x)))))))) = x

  i : is-inhabited (root f)
  i = pointed-is-inhabited (8 , refl _)

  r : root f
  r = find-existing-root f i
\end{code}

We have that `pr₁ r` evaluates to `2`:

\begin{code}
  p : pr₁ r ≡ 2
  p = refl _
\end{code}

Thus, the truncation operation `is-inhabited` doesn't erase
information. We used the hidden root `a` as a bound for searching for
the minimal root.

Notice that this construction is in pure (spartan) MLTT. Now we repeat
part of the above using the existence of small truncations as an
assumption:

\begin{code}

module exit-∥∥
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

 open basic-truncation-development pt hfe
 open find-hidden-root hiding (find-existing-root)

 find-existing-root : (f : ℕ → ℕ)
                    → (∃ \(n : ℕ) → f n ≡ 0)
                    →  Σ \(n : ℕ) → f n ≡ 0
 find-existing-root f = k
  where
   γ : root f → fix (μρ f)
   γ = to-fix (μρ f) (μρ-wconstant f)

   g : ∥ root f ∥ → fix (μρ f)
   g = ∥∥-recursion (fix-is-subsingleton (μρ f) (μρ-wconstant f)) γ

   h : fix (μρ f) → root f
   h = from-fix (μρ f)

   k : ∥ root f ∥ → root f
   k = h ∘ g
\end{code}

There is another situation in which we can eliminate truncations that
is often useful in practice. The universal property of subsingleton
truncation says that we can get a function `∥ X ∥ → Y` if `Y` is a
subsingleton and we have a given function `X → Y`. Because `Y` is a
subsingleton, the given function is automatically `wconstant`. Hence
the following generalizes this to the situation in which `Y` is a set:

\begin{code}
 ∥∥-recursion-set : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                  → is-set Y
                  → (f : X → Y)
                  → wconstant f
                  → ∥ X ∥ → Y
 ∥∥-recursion-set {𝓤} {𝓥} X Y s f κ = h ∘ g
  where
   ψ : (y y' : Y) → (Σ \x → f x ≡ y) → (Σ \x' → f x' ≡ y') → y ≡ y'
   ψ y y' (x , r) (x' , r') = y    ≡⟨ r ⁻¹   ⟩
                              f x  ≡⟨ κ x x' ⟩
                              f x' ≡⟨ r'     ⟩
                              y'   ∎

   φ : (y y' : Y) → (∃ \x → f x ≡ y) → (∃ \x' → f x' ≡ y') → y ≡ y'
   φ y y' u u' = ∥∥-recursion (s y y') (λ - → ∥∥-recursion (s y y') (ψ y y' -) u') u

   P : 𝓤 ⊔ 𝓥 ̇
   P = image f

   i : is-subsingleton P
   i (y , u) (y' , u') = to-Σ-≡ (φ y y' u u' , ∃-is-subsingleton _ _)

   g : ∥ X ∥ → P
   g = ∥∥-recursion i (corestriction f)

   h : P → Y
   h = restriction f
\end{code}

For the sake of completeness, we redevelop part of the above with `∥_∥` in place of `is-inhabited`:

\begin{code}
 wconstant-endomap-gives-∥∥-choice-function : {X : 𝓤 ̇ }
                                            → wconstant-endomap X
                                            → (∥ X ∥ → X)

 wconstant-endomap-gives-∥∥-choice-function {𝓤} {X} (f , κ) = from-fix f ∘ γ
  where
   γ : ∥ X ∥ → fix f
   γ = ∥∥-recursion (fix-is-subsingleton f κ) (to-fix f κ)


 ∥∥-choice-function-gives-wconstant-endomap : {X : 𝓤 ̇ }
                                           → (∥ X ∥ → X)
                                           → wconstant-endomap X

 ∥∥-choice-function-gives-wconstant-endomap {𝓤} {X} c = f , κ
  where
   f : X → X
   f = c ∘ ∣_∣

   κ : wconstant f
   κ x y = ap c (∥∥-is-subsingleton ∣ x ∣ ∣ y ∣)
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="choice"></a> Choice in univalent mathematics

We discuss unique choice, univalent choice and global choice.

  1. A simple form of unique choice just holds in our spartan MLTT.

  1. The full form of unique choice is logically equivalent to function
     extensionality.

  1. Univalent choice implies excluded middle and is not provable or
     disprovable, but is consistent with univalence.

  1. Global choice contradicts univalence, because it is not possible
     to choose an element of every type in way that is invariant under
     automorphisms.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="unique-choice"></a> The principle of unique choice

The principle of *simple unique choice* says that

   > if for every `x : X` there is a unique `a : A x` with `R x a`,

then

   > there is a specified function `f : (x : X) → A x` such that `R x (f x)` for all `x : X`.

This just holds and is trivial, given by projection:

\begin{code}
simple-unique-choice : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

                     → ((x : X) → ∃! \(a : A x) → R x a)
                     → Σ \(f : Π A) → (x : X) → R x (f x)

simple-unique-choice X A R s = f , φ
 where
  f : (x : X) → A x
  f x = pr₁ (center (Σ \(a : A x) → R x a) (s x))

  φ : (x : X) → R x (f x)
  φ x = pr₂ (center (Σ \(a : A x) → R x a) (s x))
\end{code}

Below we also consider a
[variation](HoTT-UF-Agda.html#simple-unique-choice') of simple unique
choice that works with `∃` (truncated `Σ`) rather than `∃!`.

A full form of unique choice is Voevodsky's formulation
[`vvfunext`](HoTT-UF-Agda.html#vvfunext) of function extensionality,
which says that products of singletons are singletons. We show that this
is equivalent to our official formulation of unique choice:

\begin{code}
Unique-Choice : (𝓤 𝓥 𝓦 : Universe) → (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇
Unique-Choice 𝓤 𝓥 𝓦 = (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )
                     → ((x : X) → ∃! \(a : A x) → R x a)
                     → ∃! \(f : Π A) → (x : X) → R x (f x)


vvfunext-gives-unique-choice : vvfunext 𝓤 (𝓥 ⊔ 𝓦) → Unique-Choice 𝓤 𝓥 𝓦
vvfunext-gives-unique-choice vv X A R s = c
 where
  a : ((x : X) → Σ \(a : A x) → R x a)
    ≃ (Σ \(f : (x : X) → A x) → (x : X) → R x (f x))

  a = ΠΣ-distr-≃

  b : is-singleton ((x : X) → Σ \(a : A x) → R x a)
  b = vv s

  c : is-singleton (Σ \(f : (x : X) → A x) → (x : X) → R x (f x))
  c = equiv-to-singleton' a b


unique-choice-gives-vvfunext : Unique-Choice 𝓤 𝓥 𝓥 → vvfunext 𝓤 𝓥
unique-choice-gives-vvfunext {𝓤} {𝓥} uc {X} {A} φ = γ
 where
  R : (x : X) → A x → 𝓥  ̇
  R x a = A x

  s' : (x : X) → is-singleton (A x × A x)
  s' x = ×-is-singleton (φ x) (φ x)

  s : (x : X) → ∃! \(y : A x) → R x y
  s = s'

  e : ∃! \(f : Π A) → (x : X) → R x (f x)
  e = uc X A R s

  e' : is-singleton (Π A × Π A)
  e' = e

  ρ : Π A ◁ Π A × Π A
  ρ = pr₁ , (λ y → y , y) , refl

  γ : is-singleton (Π A)
  γ = retract-of-singleton ρ e'
\end{code}

The above is not quite the converse of the previous, as there is a
universe mismatch, but we do get a logical equivalence by taking `𝓦`
to be `𝓥`:

\begin{code}
unique-choice⇔vvfunext : Unique-Choice 𝓤 𝓥 𝓥 ⇔ vvfunext 𝓤 𝓥
unique-choice⇔vvfunext = unique-choice-gives-vvfunext ,
                         vvfunext-gives-unique-choice
\end{code}

We now give a different derivation of unique choice from function
extensionality, in order to illustrate transport along the inverse of
`happly`. For simplicity, we assume global function extensionality in
the next few constructions.

\begin{code}
module _ (hfe : global-hfunext) where

 private
   hunapply : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g
   hunapply = inverse (happly _ _) (hfe _ _)


 transport-hunapply : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )
                      (f g : Π A)
                      (φ : (x : X) → R x (f x))
                      (h : f ∼ g)
                      (x : X)
                    → transport (λ - → (x : X) → R x (- x)) (hunapply h) φ x
                    ≡ transport (R x) (h x) (φ x)

 transport-hunapply A R f g φ h x =

   transport (λ - → ∀ x → R x (- x)) (hunapply h) φ x ≡⟨ i  ⟩
   transport (R x) (happly f g (hunapply h) x) (φ x)  ≡⟨ ii ⟩
   transport (R x) (h x) (φ x)                        ∎

  where
   a : {f g : Π A} {φ : ∀ x → R x (f x)} (p : f ≡ g) (x : domain A)
     → transport (λ - → ∀ x → R x (- x)) p φ x
     ≡ transport (R x) (happly f g p x) (φ x)

   a (refl _) x = refl _

   b : happly f g (hunapply h) ≡ h
   b = inverse-is-section (happly f g) (hfe f g) h

   i  = a (hunapply h) x
   ii = ap (λ - → transport (R x) (- x) (φ x)) b


 unique-choice : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

               → ((x : X) → ∃! \(a : A x) → R x a)
               → ∃! \(f : (x : X) → A x) → (x : X) → R x (f x)

 unique-choice X A R s = C , Φ
  where
   f₀ : (x : X) → A x
   f₀ x = pr₁ (center (Σ \(a : A x) → R x a) (s x))

   φ₀ : (x : X) → R x (f₀ x)
   φ₀ x = pr₂ (center (Σ \(a : A x) → R x a) (s x))

   C : Σ \(f : (x : X) → A x) → (x : X) → R x (f x)
   C = f₀ , φ₀

   c : (x : X) → (τ : Σ \(a : A x) → R x a) → f₀ x , φ₀ x ≡ τ
   c x = centrality (Σ \(a : A x) → R x a) (s x)

   c₁ : (x : X) (a : A x) (r : R x a) → f₀ x ≡ a
   c₁ x a r = ap pr₁ (c x (a , r))

   c₂ : (x : X) (a : A x) (r : R x a)
      → transport (λ - → R x (pr₁ -)) (c x (a , r)) (φ₀ x) ≡ r

   c₂ x a r = apd pr₂ (c x (a , r))

   Φ : (σ : Σ \(f : (x : X) → A x) → (x : X) → R x (f x)) → C ≡ σ
   Φ (f , φ) = to-Σ-≡ (p , hunapply q)
    where
     p : f₀ ≡ f
     p = hunapply (λ x → c₁ x (f x) (φ x))

     q : transport (λ - → (x : X) → R x (- x)) p φ₀ ∼ φ
     q x = transport (λ - → (x : X) → R x (- x)) p φ₀ x           ≡⟨ i   ⟩
           transport (R x) (ap pr₁ (c x (f x , φ x))) (φ₀ x)      ≡⟨ ii  ⟩
           transport (λ σ → R x (pr₁ σ)) (c x (f x , φ x)) (φ₀ x) ≡⟨ iii ⟩
           φ x                                                    ∎
      where
       i   = transport-hunapply A R f₀ f φ₀ (λ x → c₁ x (f x) (φ x)) x
       ii  = (transport-ap (R x) pr₁ (c x (f x , φ x)) (φ₀ x))⁻¹
       iii = c₂ x (f x) (φ x)
\end{code}

[Simple unique choice](HoTT-UF-Agda.html#simple-unique-choice) can be
reformulated as follows using `∃` rather than `∃!`. The statement

   > `is-subsingleton (Σ \(a : A x) → R x a)`

can be read as

   > there is at most one `a : A x` with `R x a`.

So the hypothesis of the following is that there is at most one such
`a` and at least one such `a`, which amounts to saying that there is a
unique such `a`, and hence `simple-unique-choice'` amounts to the same
things as `simple-unique-choice`. However, `simple-unique-choice` can
be formulated and proved in our spartan MLTT, whereas
`simple-unique-choice'` requires the assumption of the existence of
subsingleton truncations so that `∃` is available for its formulation.

\begin{code}
module choice
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

  open basic-truncation-development pt hfe public

  simple-unique-choice' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

                        → ((x : X) → is-subsingleton (Σ \(a : A x) → R x a))

                        → ((x : X) → ∃ \(a : A x) → R x a)
                        → Σ \(f : Π A) → (x : X) → R x (f x)

  simple-unique-choice' X A R u φ = simple-unique-choice X A R s
   where
    s : (x : X) → ∃! \(a : A x) → R x a
    s x = inhabited-subsingletons-are-singletons (Σ \(a : A x) → R x a) (φ x) (u x)
\end{code}

In the next few subsections we continue working within the submodule
`choice`, in order to have the existence of propositional truncations
available, so that we can use the existential quantifier `∃`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="univalent-choice"></a> The univalent axiom of choice

The axiom of choice in univalent mathematics says that

   > if for every `x : X` there exists `a : A x` with `R x a`,

where `R` is some given relation,

   > then there exists a choice function `f : (x : X) → A x` with `R x (f x)` for all `x : X`,

provided

 1. `X` is a set,
 1. `A` is a family of sets,
 1. the relation `R` is subsingleton valued.

This is not provable or disprovable in univalent mathematics, but,
with this proviso, it does hold in [Voevodsky's simplicial
model](https://arxiv.org/abs/1211.2851) of our univalent type theory,
and hence is consistent. It is important that we have the condition
that `A` is a set-indexed family of sets and that the relation `R` is
subsingleton valued. For arbitrary higher groupoids, it is not in
general possible to perform the choice functorially.

\begin{code}
  AC : ∀ 𝓣 (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X → ((x : X) → is-set (A x)) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇

  AC 𝓣 X A i j = (R : (x : X) → A x → 𝓣 ̇ )
               → ((x : X) (a : A x) → is-subsingleton (R x a))

               → ((x : X) → ∃ \(a : A x) → R x a)
               → ∃ \(f : Π A) → (x : X) → R x (f x)
\end{code}

We define the axiom of choice in the universe `𝓤` to be the above with
`𝓣 = 𝓤`, for all possible `X` and `A` (and `R`).

\begin{code}
  Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
  Choice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (A x))
           → AC 𝓤 X A i j
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="univalent-choice2"></a> A second formulation of univalent choice

The above is equivalent to another familiar formulation of choice,
namely that a set-indexed product of non-empty sets is non-empty,
where in a constructive setting we strengthen `non-empty` to
`inhabited` (but this strengthening is immaterial, because choice
implies excluded middle, and excluded middle implies that
non-emptiness and inhabitation are the same notion).

\begin{code}
  IAC : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-set (Y x)) → 𝓤 ⊔ 𝓥 ̇
  IAC X Y i j = ((x : X) → ∥ Y x ∥) → ∥ Π Y ∥

  IChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  IChoice 𝓤 = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (Y x))
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

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="univalent-choice3"></a> A third formulation of univalent choice

\begin{code}
  TAC : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-set (A x)) → 𝓤 ⊔ 𝓥 ̇
  TAC X A i j = ∥((x : X) → ∥ A x ∥ → A x)∥


  TChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  TChoice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (A x))
            → TAC X A i j
\end{code}

Notice that we use the hypothesis twice to get the conclusion in the
following:

\begin{code}
  IChoice-gives-TChoice : IChoice 𝓤 → TChoice 𝓤
  IChoice-gives-TChoice {𝓤} iac X A i j = γ
   where
    B : (x : X) → ∥ A x ∥ → 𝓤 ̇
    B x s = A x

    k : (x : X) (s : ∥ A x ∥) → is-set (B x s)
    k x s = j x

    l : (x : X) → is-set ∥ A x ∥
    l x = subsingletons-are-sets ∥ A x ∥ ∥∥-is-subsingleton

    m : (x : X) →  is-set (∥ A x ∥ → A x)
    m x = Π-is-set hfe (λ s → j x)

    φ : (x : X) → ∥ (∥ A x ∥ → A x) ∥
    φ x = iac ∥ A x ∥ (B x) (l x) (k x) (𝑖𝑑 ∥ A x ∥)

    γ : ∥((x : X) → ∥ A x ∥ → A x)∥
    γ = iac X (λ x → ∥ A x ∥ → A x) i m φ


  TChoice-gives-IChoice : TChoice 𝓤 → IChoice 𝓤
  TChoice-gives-IChoice tac X A i j = γ
   where
    γ : ((x : X) → ∥ A x ∥) → ∥ Π A ∥
    γ g = ∥∥-functor φ (tac X A i j)
     where
      φ : ((x : X) → ∥ A x ∥ → A x) → Π A
      φ f x = f x (g x)
\end{code}

*Exercise*. A fourth formulation of the axiom of choice is that every
 surjection of sets has an unspecified section.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="choice-gives-excluded middle"></a> Univalent choice gives excluded middle

We apply the third formulation to show that choice implies excluded
middle. We begin with the following lemma.

\begin{code}
  decidable-equality-criterion : {X : 𝓤 ̇ } (α : 𝟚 → X)
                               → ((x : X) → (∃ \(n : 𝟚) → α n ≡ x)
                                          → (Σ \(n : 𝟚) → α n ≡ x))
                               → decidable(α ₀ ≡ α ₁)

  decidable-equality-criterion α c = γ d
   where
    r : 𝟚 → image α
    r = corestriction α

    σ : (y : image α) → Σ \(n : 𝟚) → r n ≡ y
    σ (x , t) = f u
     where
      u : Σ \(n : 𝟚) → α n ≡ x
      u = c x t

      f : (Σ \(n : 𝟚) → α n ≡ x) → Σ \(n : 𝟚) → r n ≡ (x , t)
      f (n , p) = n , to-Σ-≡ (p , ∥∥-is-subsingleton _ t)

    s : image α → 𝟚
    s y = pr₁ (σ y)

    η : (y : image α) → r (s y) ≡ y
    η y = pr₂ (σ y)

    l : left-cancellable s
    l = sections-are-lc s (r , η)

    αr : {m n : 𝟚} → α m ≡ α n → r m ≡ r n
    αr p = to-Σ-≡ (p , ∥∥-is-subsingleton _ _)

    rα : {m n : 𝟚} → r m ≡ r n → α m ≡ α n
    rα = ap pr₁

    αs : {m n : 𝟚} → α m ≡ α n → s (r m) ≡ s (r n)
    αs p = ap s (αr p)

    sα : {m n : 𝟚} → s (r m) ≡ s (r n) → α m ≡ α n
    sα p = rα (l p)

    γ : decidable (s (r ₀) ≡ s (r ₁)) → decidable(α ₀ ≡ α ₁)
    γ (inl p) = inl (sα p)
    γ (inr u) = inr (contrapositive αs u)

    d : decidable (s (r ₀) ≡ s (r ₁))
    d = 𝟚-has-decidable-equality (s (r ₀)) (s (r ₁))
\end{code}

The first consequence of this lemma is that choice implies that every
set has decidable equality.

\begin{code}
  choice-gives-decidable-equality : TChoice 𝓤
                                  → (X : 𝓤 ̇ ) → is-set X → has-decidable-equality X

  choice-gives-decidable-equality {𝓤} tac X i x₀ x₁ = γ
   where
    α : 𝟚 → X
    α ₀ = x₀
    α ₁ = x₁

    A : X → 𝓤 ̇
    A x = Σ \(n : 𝟚) → α n ≡ x

    l : is-subsingleton (decidable (x₀ ≡ x₁))
    l = +-is-subsingleton' hunapply (i (α ₀) (α ₁))

    δ : ∥((x : X) → ∥ A x ∥ → A x)∥ → decidable(x₀ ≡ x₁)
    δ = ∥∥-recursion l (decidable-equality-criterion α)

    j : (x : X) → is-set (A x)
    j x = subsets-of-sets-are-sets 𝟚 (λ n → α n ≡ x) 𝟚-is-set (λ n → i (α n) x)

    h : ∥((x : X) → ∥ A x ∥ → A x)∥
    h = tac X A i j

    γ : decidable (x₀ ≡ x₁)
    γ = δ h
\end{code}

Applying the above to the object `Ω 𝓤` of truth-values in the universe
`𝓤`, we get excluded middle:

\begin{code}
  choice-gives-EM : propext 𝓤 → TChoice (𝓤 ⁺) → EM 𝓤
  choice-gives-EM {𝓤} pe tac = em
   where
    ⊤ : Ω 𝓤
    ⊤ = (Lift 𝓤 𝟙 , equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton)

    δ : (ω : Ω 𝓤) → decidable (⊤ ≡ ω)
    δ = choice-gives-decidable-equality tac (Ω 𝓤) (Ω-is-a-set hunapply pe) ⊤

    em : (P : 𝓤 ̇ ) → is-subsingleton P → P + ¬ P
    em P i = γ (δ (P , i))
     where
      γ : decidable (⊤ ≡ (P , i)) → P + ¬ P

      γ (inl r) = inl (Id→fun s (lift ⋆))
       where
        s : Lift 𝓤 𝟙 ≡ P
        s = ap pr₁ r

      γ (inr n) = inr (contrapositive f n)
       where
        f : P → ⊤ ≡ P , i
        f p = Ω-ext hunapply pe (λ (_ : Lift 𝓤 𝟙) → p) (λ (_ : P) → lift ⋆)
\end{code}

For more information with Agda code, see
[this](https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Choice.html).

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="global-choice"></a> Global choice

The following says that, for any given `X`, we can either choose a
point of `X` or tell that `X` is empty:

\begin{code}
  global-choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
  global-choice 𝓤 = (X : 𝓤 ̇ ) → X + is-empty X
\end{code}

And the following says that we can pick a point of every inhabited
type:

\begin{code}
  global-∥∥-choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
  global-∥∥-choice 𝓤 = (X : 𝓤 ̇ ) → ∥ X ∥ → X
\end{code}

We first show that these two forms of global choice are logically
equivalent, where one direction requires propositional extensionality
(in addition to function extensionality, which is an assumption for
this module).

\begin{code}
  open exit-∥∥ pt hfe

  global-choice-gives-wconstant : global-choice 𝓤
                                → (X : 𝓤 ̇ ) → wconstant-endomap X

  global-choice-gives-wconstant g X = decidable-has-wconstant-endomap (g X)


  global-choice-gives-global-∥∥-choice : global-choice  𝓤
                                       → global-∥∥-choice 𝓤

  global-choice-gives-global-∥∥-choice {𝓤} c X = γ (c X)
   where
    γ : X + is-empty X → ∥ X ∥ → X
    γ (inl x) s = x
    γ (inr n) s = !𝟘 X (∥∥-recursion 𝟘-is-subsingleton n s)


  global-∥∥-choice-gives-all-types-are-sets : global-∥∥-choice 𝓤
                                            → (X : 𝓤 ̇ ) → is-set  X

  global-∥∥-choice-gives-all-types-are-sets {𝓤} c X =
    types-with-wconstant-≡-endomaps-are-sets X
        (λ x y → ∥∥-choice-function-gives-wconstant-endomap (c (x ≡ y)))


  global-∥∥-choice-gives-universe-is-set : global-∥∥-choice (𝓤 ⁺)
                                         → is-set (𝓤 ̇ )

  global-∥∥-choice-gives-universe-is-set {𝓤} c =
    global-∥∥-choice-gives-all-types-are-sets c (𝓤 ̇)


  global-∥∥-choice-gives-choice : global-∥∥-choice 𝓤
                                → TChoice 𝓤

  global-∥∥-choice-gives-choice {𝓤} c X A i j = ∣(λ x → c (A x))∣


  global-∥∥-choice-gives-EM : propext 𝓤
                            → global-∥∥-choice (𝓤 ⁺)
                            → EM  𝓤

  global-∥∥-choice-gives-EM {𝓤} pe c =
    choice-gives-EM pe (global-∥∥-choice-gives-choice c)


  global-∥∥-choice-gives-global-choice : propext 𝓤
                                       → global-∥∥-choice 𝓤
                                       → global-∥∥-choice (𝓤 ⁺)
                                       → global-choice 𝓤

  global-∥∥-choice-gives-global-choice {𝓤} pe c c⁺ X = γ
   where
    d : decidable ∥ X ∥
    d = global-∥∥-choice-gives-EM pe c⁺ ∥ X ∥ ∥∥-is-subsingleton

    f : decidable ∥ X ∥ → X + is-empty X
    f (inl i) = inl (c X i)
    f (inr φ) = inr (contrapositive ∣_∣ φ)

    γ : X + is-empty X
    γ = f d


  Global-Choice Global-∥∥-Choice : 𝓤ω
  Global-Choice    = ∀ 𝓤 → global-choice  𝓤
  Global-∥∥-Choice = ∀ 𝓤 → global-∥∥-choice 𝓤


  Global-Choice-gives-Global-∥∥-Choice : Global-Choice → Global-∥∥-Choice
  Global-Choice-gives-Global-∥∥-Choice c 𝓤 =
    global-choice-gives-global-∥∥-choice (c 𝓤)


  Global-∥∥-Choice-gives-Global-Choice : global-propext
                                       → Global-∥∥-Choice → Global-Choice
  Global-∥∥-Choice-gives-Global-Choice pe c 𝓤 =
    global-∥∥-choice-gives-global-choice pe (c 𝓤) (c (𝓤 ⁺))
\end{code}

\begin{code}
  global-∥∥-choice-inconsistent-with-univalence : Global-∥∥-Choice
                                                → Univalence
                                                → 𝟘

  global-∥∥-choice-inconsistent-with-univalence g ua = γ (g 𝓤₁) (ua 𝓤₀)
   where
    open example-of-a-nonset (ua 𝓤₀)

    γ : global-∥∥-choice 𝓤₁ → is-univalent 𝓤₀ → 𝟘
    γ g ua = 𝓤₀-is-not-a-set (global-∥∥-choice-gives-all-types-are-sets g (𝓤₀ ̇ ))


  global-choice-inconsistent-with-univalence : Global-Choice
                                             → Univalence
                                             → 𝟘

  global-choice-inconsistent-with-univalence g =
    global-∥∥-choice-inconsistent-with-univalence
      (Global-Choice-gives-Global-∥∥-Choice g)
\end{code}

See also Theorem 3.2.2 and Corollary 3.2.7 of the HoTT book for a
different argument that works with a single, arbitrary universe.

Notice also that, without using propositional extensionality, we have:

\begin{code}
  global-choice-gives-all-types-are-sets : global-choice 𝓤
                                         → (X : 𝓤 ̇ ) → is-set  X

  global-choice-gives-all-types-are-sets {𝓤} c X = hedberg (λ x y → c (x ≡ y))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="resizing"></a> Propositional resizing, truncation and the powerset

Voevodsky [considered resizing
rules](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf)
for a type theory for univalent foundations. These rules govern the
syntax of the formal system, and hence are of a meta-mathematical
nature.

Here we instead formulate, in our type theory without such rules,
mathematical resizing principles. These principles are provable in the
system with Voevodsky's rules.

The consistency of the resizing *rules* is an open problem at the time
of writing, but the resizing *principles* are consistent relative to ZFC
with Grothendieck universes, because they follow from excluded middle,
which is known to be validated by the simplicial-set model.

It is also an open problem whether the resizing principles discussed
below have a computational interpretation.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="prop-resizing"></a> Propositional resizing

We say that a type `X` has size `𝓥` if it is equivalent to a type in the
universe `𝓥`:

\begin{code}
_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
X has-size 𝓥 = Σ \(Y : 𝓥 ̇ ) → X ≃ Y
\end{code}

The propositional resizing principle from a universe `𝓤` to a universe
`𝓥` says that every subsingleton in `𝓤` has size `𝓥`:

\begin{code}
propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇ ) → is-subsingleton P → P has-size 𝓥
\end{code}

Propositional resizing from a universe to a higher universe just
holds, of course:

\begin{code}
resize-up : (X : 𝓤 ̇ ) → X has-size (𝓤 ⊔ 𝓥)
resize-up {𝓤} {𝓥} X = (Lift 𝓥 X , ≃-Lift X)

resize-up-subsingleton : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-subsingleton {𝓤} {𝓥} P i = resize-up {𝓤} {𝓥} P
\end{code}

We use the following to work with propositional resizing more abstractly:

\begin{code}
resize : propositional-resizing 𝓤 𝓥
       → (P : 𝓤 ̇ ) (i : is-subsingleton P) → 𝓥 ̇

resize ρ P i = pr₁ (ρ P i)


resize-is-subsingleton : (ρ : propositional-resizing 𝓤 𝓥)
                         (P : 𝓤 ̇ ) (i : is-subsingleton P)
                       → is-subsingleton (resize ρ P i)

resize-is-subsingleton ρ P i = equiv-to-subsingleton (≃-sym (pr₂ (ρ P i))) i


to-resize : (ρ : propositional-resizing 𝓤 𝓥)
            (P : 𝓤 ̇ ) (i : is-subsingleton P)
          → P → resize ρ P i

to-resize ρ P i = Eq→fun (pr₂ (ρ P i))


from-resize : (ρ : propositional-resizing 𝓤 𝓥)
              (P : 𝓤 ̇ ) (i : is-subsingleton P)
            → resize ρ P i → P

from-resize ρ P i = Eq→fun (≃-sym(pr₂ (ρ P i)))


Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="em-resizing"></a> Excluded middle gives propositional resizing

Propositional resizing is consistent, because it is implied by
excluded middle, which is consistent (with or without univalence):

\begin{code}
EM-gives-PR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-PR {𝓤} {𝓥} em P i = Q (em P i) , e
 where
   Q : P + ¬ P → 𝓥 ̇
   Q (inl p) = Lift 𝓥 𝟙
   Q (inr n) = Lift 𝓥 𝟘

   j : (d : P + ¬ P) → is-subsingleton (Q d)
   j (inl p) = equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton
   j (inr n) = equiv-to-subsingleton (Lift-≃ 𝟘) 𝟘-is-subsingleton

   f : (d : P + ¬ P) → P → Q d
   f (inl p) p' = lift ⋆
   f (inr n) p  = !𝟘 (Lift 𝓥 𝟘) (n p)

   g : (d : P + ¬ P) → Q d → P
   g (inl p) q = p
   g (inr n) q = !𝟘 P (lower q)

   e : P ≃ Q (em P i)
   e = logically-equivalent-subsingletons-are-equivalent
        P (Q (em P i)) i (j (em P i)) (f (em P i) , g (em P i))
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="resizing-subsingleton"></a> The propositional resizing axiom is a subsingleton

To show that the propositional resizing principle is a subsingleton,
we use univalence here.

\begin{code}
has-size-is-subsingleton : Univalence
                         → (X : 𝓤 ̇ ) (𝓥 :  Universe)
                         → is-subsingleton (X has-size 𝓥)

has-size-is-subsingleton {𝓤} ua X 𝓥 = univalence→' (ua 𝓥) (ua (𝓤 ⊔ 𝓥)) X


PR-is-subsingleton : Univalence → is-subsingleton (propositional-resizing 𝓤 𝓥)
PR-is-subsingleton {𝓤} {𝓥} ua =
 Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ P → Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ i → has-size-is-subsingleton ua P 𝓥))
\end{code}

*Exercise*. [It is
possible](https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Resizing.html) to
show that the propositional resizing principle is a subsingleton
using propositional and functional extensionality instead of
univalence.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="prop-impred"></a> Propositional impredicativity

We consider two notions of propositional impredicativity:

\begin{code}
Impredicativity : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Impredicativity 𝓤 𝓥 = (Ω 𝓤) has-size 𝓥

is-impredicative : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-impredicative 𝓤 = Impredicativity 𝓤 𝓤

PR-gives-Impredicativity⁺ : global-propext
                          → global-dfunext
                          → propositional-resizing 𝓥 𝓤
                          → propositional-resizing 𝓤 𝓥
                          → Impredicativity 𝓤 (𝓥 ⁺)

PR-gives-Impredicativity⁺ {𝓥} {𝓤} pe fe ρ σ = γ
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-subsingleton ρ Q j

  ψ : Ω 𝓤 → Ω 𝓥
  ψ (P , i) = resize σ P i , resize-is-subsingleton σ P i

  η : (p : Ω 𝓤) → φ (ψ p) ≡ p
  η (P , i) = Ω-ext fe pe a b
   where
    Q : 𝓥 ̇
    Q = resize σ P i

    j : is-subsingleton Q
    j = resize-is-subsingleton σ P i

    a : resize ρ Q j → P
    a = from-resize σ P i ∘ from-resize ρ Q j

    b : P → resize ρ Q j
    b = to-resize ρ Q j ∘ to-resize σ P i

  ε : (q : Ω 𝓥) → ψ (φ q) ≡ q
  ε (Q , j) = Ω-ext fe pe a b
   where
    P : 𝓤 ̇
    P = resize ρ Q j

    i : is-subsingleton P
    i = resize-is-subsingleton ρ Q j

    a : resize σ P i → Q
    a = from-resize ρ Q j ∘ from-resize σ P i

    b : Q → resize σ P i
    b = to-resize σ P i ∘ to-resize ρ Q j

  γ : (Ω 𝓤) has-size (𝓥 ⁺)
  γ = Ω 𝓥 , invertibility-gives-≃ ψ (φ , η , ε)
\end{code}

Propositional resizing doesn't imply that the first universe 𝓤₀ is
propositionally impredicative, but it does imply that all other,
successor, universes 𝓤 ⁺ are.

\begin{code}
PR-gives-impredicativity⁺ : global-propext
                          → global-dfunext
                          → propositional-resizing (𝓤 ⁺) 𝓤
                          → is-impredicative (𝓤 ⁺)

PR-gives-impredicativity⁺ pe fe = PR-gives-Impredicativity⁺
                                   pe fe (λ P i → resize-up P)
\end{code}

What we get with propositional resizing is that all types of
subsingletons of any universe 𝓤 are equivalent to Ω 𝓤₀, which lives in
the second universe 𝓤₁:

\begin{code}
PR-gives-impredicativity₁ : global-propext
                          → global-dfunext
                          → propositional-resizing 𝓤 𝓤₀
                          → Impredicativity 𝓤 𝓤₁

PR-gives-impredicativity₁ pe fe = PR-gives-Impredicativity⁺
                                   pe fe (λ P i → resize-up P)
\end{code}

*Exercise*. Excluded middle
[gives](https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Resizing.html) the
impredicativity of the first universe, and of all other universes.

We also have that moving `Ω` around universes moves subsingletons around
universes:

\begin{code}
Impredicativity-gives-PR : propext 𝓤
                         → dfunext 𝓤 𝓤
                         → Impredicativity 𝓤 𝓥
                         → propositional-resizing 𝓤 𝓥

Impredicativity-gives-PR {𝓤} {𝓥} pe fe (O , e) P i = Q , ε
 where
  𝟙' : 𝓤 ̇
  𝟙' = Lift 𝓤 𝟙

  k : is-subsingleton 𝟙'
  k (lift ⋆) (lift ⋆) = refl (lift ⋆)

  down : Ω 𝓤 → O
  down = Eq→fun e

  O-is-set : is-set O
  O-is-set = equiv-to-set (≃-sym e) (Ω-is-a-set fe pe)

  Q : 𝓥 ̇
  Q = down (𝟙' , k) ≡ down (P , i)

  j : is-subsingleton Q
  j = O-is-set (down (Lift 𝓤 𝟙 , k)) (down (P , i))

  φ : Q → P
  φ q = Id→fun
         (ap _holds (equivs-are-lc down (Eq→fun-is-equiv e) q))
         (lift ⋆)

  γ : P → Q
  γ p = ap down (to-Σ-≡ (pe k i (λ _ → p) (λ _ → lift ⋆) ,
                         being-subsingleton-is-subsingleton fe _ _))

  ε : P ≃ Q
  ε = logically-equivalent-subsingletons-are-equivalent P Q i j (γ , φ)
\end{code}

*Exercise*. `propext` and `funext` and excluded middle together imply
[that](https://www.cs.bham.ac.uk/~mhe/agda-new/UF-Resizing.html) `Ω 𝓤`
has size `𝓤₀`.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="truncation-from-resizing"></a> Propositional resizing gives subsingleton truncation

Using Voevodsky's [construction](HoTT-UF-Agda.html#truncation) and
propositional resizing, we get that function extensionality implies
that subsingleton truncations exist:

\begin{code}
PR-gives-existence-of-truncations : global-dfunext
                                  → Propositional-resizing
                                  → subsingleton-truncations-exist

PR-gives-existence-of-truncations fe R =
 record
 {
   ∥_∥ =

    λ {𝓤} X → resize R
               (is-inhabited X)
               (inhabitation-is-subsingleton fe X) ;

   ∥∥-is-subsingleton =

    λ {𝓤} {X} → resize-is-subsingleton R
                 (is-inhabited X)
                 (inhabitation-is-subsingleton fe X) ;

   ∣_∣ =

    λ {𝓤} {X} x → to-resize R
                   (is-inhabited X)
                   (inhabitation-is-subsingleton fe X)
                   (pointed-is-inhabited x) ;

   ∥∥-recursion =

    λ {𝓤} {𝓥} {X} {P} i u s → from-resize R P i
                                (inhabited-recursion X
                                  (resize R P i)
                                  (resize-is-subsingleton R P i)
                                  (to-resize R P i ∘ u)
                                  (from-resize R
                                    (is-inhabited X)
                                    (inhabitation-is-subsingleton fe X) s))
 }
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="powerset-resizing"></a> The powerset in the presence of propositional resizing

As a second, important, use of resizing, we revisit the powerset.
First, given a set of subsets, that is, an element of the double
powerset, we would like to consider its union. We investigate its
existence in a submodule with assumptions.

\begin{code}
module powerset-union-existence
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

 open basic-truncation-development pt hfe
\end{code}

Unions of *families* of subsets exist under the above assumption of
the existence of truncations, provided the index set `I` is in a universe
equal or below the universe of the type `X` we take the powerset of:

\begin{code}
 family-union : {X : 𝓤 ⊔ 𝓥 ̇ } {I : 𝓥 ̇ } → (I → 𝓟 X) → 𝓟 X
 family-union {𝓤} {𝓥} {X} {I} A = λ x → (∃ \(i : I) → x ∈ A i) , ∃-is-subsingleton
\end{code}

Notice the increase of universe levels in the iteration of powersets:

\begin{code}
 𝓟𝓟 : 𝓤 ̇ → 𝓤 ⁺⁺ ̇
 𝓟𝓟 X = 𝓟 (𝓟 X)
\end{code}

The following doesn't assert that unions of collections of subsets are
available. It says what it means for them to be available:

\begin{code}
 existence-of-unions : (𝓤 : Universe) → 𝓤 ⁺⁺ ̇
 existence-of-unions 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : 𝓟𝓟 X)
     → Σ \(B : 𝓟 X)
             → (x : X) → (x ∈ B) ⇔ ∃ \(A : 𝓟 X) → (A ∈ 𝓐) × (x ∈ A)
\end{code}

One may wonder whether there are different universe assignments for
the above definition, for instance whether we can instead assume `𝓐 :
(X → Ω 𝓥) → Ω 𝓦` for suitable universes `𝓥` and `𝓦`, possibly
depending on `𝓤`. That this is not the case can be checked by writing
the above definition in the following alternative form:

\begin{code}
 existence-of-unions₁ : (𝓤 :  Universe) → _ ̇
 existence-of-unions₁ 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : (X → Ω _) → Ω _)
     → Σ \(B : X → Ω _)
             → (x : X) → (x ∈ B) ⇔ ∃ \(A : X → Ω _) → (A ∈ 𝓐) × (x ∈ A)
\end{code}

The fact that Agda accepts the above definition without errors means
that there is a unique way to fill each `_`, which has to be the
following.

\begin{code}
 existence-of-unions₂ : (𝓤 :  Universe) → 𝓤 ⁺⁺ ̇
 existence-of-unions₂ 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : (X → Ω 𝓤) → Ω (𝓤 ⁺))
     → Σ \(B : X → Ω 𝓤)
             → (x : X) → (x ∈ B) ⇔ ∃ \(A : X → Ω 𝓤) → (A ∈ 𝓐) × (x ∈ A)

 existence-of-unions-agreement : existence-of-unions 𝓤 ≡ existence-of-unions₂ 𝓤
 existence-of-unions-agreement = refl _
\end{code}

To get the universe assigments explicitly, using Agda's interactive
mode, we can write holes `?` instead of `_` and then ask Agda to fill
them uniquely by solving constrains, which is what we did to construct
`existence-of-unions₂`.

*Exercise*. Show that the existence of unions is a subsingleton type.

Without propositional resizing principles, it is not possible to
establish the existence.

\begin{code}
 existence-of-unions-gives-PR : existence-of-unions 𝓤
                              → propositional-resizing (𝓤 ⁺) 𝓤

 existence-of-unions-gives-PR {𝓤} α = γ
  where
   γ : (P : 𝓤 ⁺ ̇ ) → (i : is-subsingleton P) → P has-size 𝓤
   γ P i = Q , e
    where
    𝟙ᵤ : 𝓤 ̇
    𝟙ᵤ = Lift 𝓤 𝟙

    ⋆ᵤ : 𝟙ᵤ
    ⋆ᵤ = lift ⋆

    𝟙ᵤ-is-subsingleton : is-subsingleton 𝟙ᵤ
    𝟙ᵤ-is-subsingleton = equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton

    𝓐 : 𝓟𝓟 𝟙ᵤ
    𝓐 = λ (A : 𝓟 𝟙ᵤ) → P , i

    B : 𝓟 𝟙ᵤ
    B = pr₁ (α 𝟙ᵤ 𝓐)

    φ : (x : 𝟙ᵤ) → (x ∈ B) ⇔ ∃ \(A : 𝓟 𝟙ᵤ) → (A ∈ 𝓐) × (x ∈ A)
    φ = pr₂ (α 𝟙ᵤ 𝓐)

    Q : 𝓤 ̇
    Q = ⋆ᵤ ∈ B

    j : is-subsingleton Q
    j = ∈-is-subsingleton ⋆ᵤ B

    f : P → Q
    f p = b
     where
      a : Σ \(A : 𝓟 𝟙ᵤ) → (A ∈ 𝓐) × (⋆ᵤ ∈ A)
      a = (λ (x : 𝟙ᵤ) → 𝟙ᵤ , 𝟙ᵤ-is-subsingleton) , p , ⋆ᵤ

      b : ⋆ᵤ ∈ B
      b = rl-implication (φ ⋆ᵤ) ∣ a ∣

    g : Q → P
    g q = ∥∥-recursion i b a
     where
      a : ∃ \(A : 𝓟 𝟙ᵤ) → (A ∈ 𝓐) × (⋆ᵤ ∈ A)
      a = lr-implication (φ ⋆ᵤ) q

      b : (Σ \(A : 𝓟 𝟙ᵤ) → (A ∈ 𝓐) × (⋆ᵤ ∈ A)) → P
      b (A , m , _) = m

    e : P ≃ Q
    e = logically-equivalent-subsingletons-are-equivalent P Q i j (f , g)
\end{code}

The converse also holds, with an easier construction:

\begin{code}
 PR-gives-existence-of-unions : propositional-resizing (𝓤 ⁺) 𝓤
                              → existence-of-unions 𝓤

 PR-gives-existence-of-unions {𝓤} ρ X 𝓐 = B , (λ x → lr x , rl x)
  where
   β : X → 𝓤 ⁺ ̇
   β x = ∃ \(A : 𝓟 X) → (A ∈ 𝓐) × (x ∈ A)

   i : (x : X) → is-subsingleton (β x)
   i x = ∃-is-subsingleton

   B : 𝓟 X
   B x = (resize ρ (β x) (i x) , resize-is-subsingleton ρ (β x) (i x))

   lr : (x : X) → x ∈ B → ∃ \(A : 𝓟 X) → (A ∈ 𝓐) × (x ∈ A)
   lr x = from-resize ρ (β x) (i x)

   rl : (x : X) → (∃ \(A : 𝓟 X) → (A ∈ 𝓐) × (x ∈ A)) → x ∈ B
   rl x = to-resize ρ (β x) (i x)
\end{code}

We now close the above submodule and start another one with different
assumptions:

\begin{code}
module basic-powerset-development
        (hfe : global-hfunext)
        (ρ   : Propositional-resizing)
       where

  pt : subsingleton-truncations-exist
  pt = PR-gives-existence-of-truncations (hfunext-gives-dfunext hfe) ρ

  open basic-truncation-development pt hfe
  open powerset-union-existence pt hfe


  ⋃ : {X : 𝓤 ̇ } → 𝓟𝓟 X → 𝓟 X
  ⋃ 𝓐 = pr₁ (PR-gives-existence-of-unions ρ _ 𝓐)


  ⋃-property : {X : 𝓤 ̇ } (𝓐 : 𝓟𝓟 X)
             → (x : X) → (x ∈ ⋃ 𝓐) ⇔ ∃ \(A : 𝓟 X) → (A ∈ 𝓐) × (x ∈ A)

  ⋃-property 𝓐 = pr₂ (PR-gives-existence-of-unions ρ _ 𝓐)
\end{code}

The construction of intersections is as that of unions using
propositional resizing:

\begin{code}
  intersections-exist :
    (X : 𝓤 ̇ )
    (𝓐 : 𝓟𝓟 X)
       → Σ \(B : 𝓟 X)
               → (x : X) → (x ∈ B) ⇔ ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A)

  intersections-exist {𝓤} X 𝓐 = B , (λ x → lr x , rl x)
   where
    β : X → 𝓤 ⁺ ̇
    β x = (A : 𝓟 X) → A ∈ 𝓐 → x ∈ A

    i : (x : X) → is-subsingleton (β x)
    i x = Π-is-subsingleton hunapply
           (λ A → Π-is-subsingleton hunapply
           (λ _ → ∈-is-subsingleton x A))

    B : 𝓟 X
    B x = (resize ρ (β x) (i x) , resize-is-subsingleton ρ (β x) (i x))

    lr : (x : X) → x ∈ B → (A : 𝓟 X) → A ∈ 𝓐 → x ∈ A
    lr x = from-resize ρ (β x) (i x)

    rl : (x : X) → ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A) → x ∈ B
    rl x = to-resize ρ (β x) (i x)


  ⋂ : {X : 𝓤 ̇ } → 𝓟𝓟 X → 𝓟 X
  ⋂ {𝓤} {X} 𝓐 = pr₁ (intersections-exist X 𝓐)


  ⋂-property : {X : 𝓤 ̇ } (𝓐 : 𝓟𝓟 X)
             → (x : X) → (x ∈ ⋂ 𝓐) ⇔ ((A : 𝓟 X) → A ∈ 𝓐 → x ∈ A)

  ⋂-property {𝓤} {X} 𝓐 = pr₂ (intersections-exist X 𝓐)


  ∅ full : {X : 𝓤 ̇ } → 𝓟 X

  ∅    = λ x → (Lift _ 𝟘 , equiv-to-subsingleton (Lift-≃ 𝟘) 𝟘-is-subsingleton)

  full = λ x → (Lift _ 𝟙 , equiv-to-subsingleton (Lift-≃ 𝟙) 𝟙-is-subsingleton)


  ∅-property : (X : 𝓤 ̇ ) → (x : X) → ¬(x ∈ ∅)
  ∅-property X x = lower


  full-property : (X : 𝓤 ̇ ) → (x : X) → x ∈ full
  full-property X x = lift ⋆


  _∩_ _∪_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓟 X

  (A ∪ B) = λ x → ((x ∈ A) ∨ (x ∈ B)) , ∨-is-subsingleton

  (A ∩ B) = λ x → ((x ∈ A) × (x ∈ B)) ,
                  ×-is-subsingleton
                    (∈-is-subsingleton x A)
                    (∈-is-subsingleton x B)


  ∪-property : {X : 𝓤 ̇ } (A B : 𝓟 X)
             → (x : X) → x ∈ (A ∪ B) ⇔ (x ∈ A) ∨ (x ∈ B)

  ∪-property {𝓤} {X} A B x = id , id


  ∩-property : {X : 𝓤 ̇ } (A B : 𝓟 X)
             → (x : X) → x ∈ (A ∩ B) ⇔ (x ∈ A) × (x ∈ B)

  ∩-property {𝓤} {X} A B x = id , id

  infix  20 _∩_
  infix  20 _∪_
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
#### <a id="topol-resizing"></a> Topological spaces in the presence of propositional resizing

For example, with this we can define the type of topological spaces as
follows, where `𝓞` consists of designated sets, conventionally called
*open* and collectively referred to as the *topology* on `X`, which are
stipulated to be closed under finite intersections and arbitrary
unions. For finite intersections we consider the unary case `full` and
the binary case `∩` . Because the empty set is the union of the empty
collection (exercise), it is automatically included among the open
sets.

\begin{code}
  Top : (𝓤 : Universe) → 𝓤 ⁺⁺ ̇
  Top 𝓤 = Σ \(X : 𝓤 ̇ )
        → is-set X
        × Σ \(𝓞 : 𝓟𝓟 X)
        → full ∈ 𝓞
        × ((U V : 𝓟 X) → U ∈ 𝓞 → V ∈ 𝓞 → (U ∩ V) ∈ 𝓞)
        × ((𝓖 : 𝓟𝓟 X) → 𝓖 ⊆ 𝓞 → ⋃ 𝓖 ∈ 𝓞)
\end{code}

Notice that this jumps two universes.  It is also possible, with
`Ω`-resizing, to construct the powerset in such a way that the powerset
of any type lives in the same universe as the type (exercise), and
hence so that the type of topological spaces in a base universe lives
in the next universe (exercise), rather than two universes above the
base universe.

*Exercise*. For a function `X → Y`, define its inverse image `𝓟 Y → 𝓟
X` and its direct image `𝓟 X → 𝓟 Y`.  Define the notion of a
continuous map of topological spaces, namely a function of the
underlying sets whose inverse images of open sets are open. Show that
the identity function is continuous and that continuous maps are
closed under composition.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="quotients"></a> Quotients

We now construct quotients using a technique proposed by Voevodsky,
who assumed propositional resizing for that purpose, so that the
quotient of a given type by a given equivalence relation would live in
the same universe as the type. But the requirement that the quotient
lives in the same universe is not needed to prove the universal
property of the quotient.

We construct the quotient using propositional truncations, assuming
functional and propositional extensionality, *without assuming
resizing*.

A binary relation `_≈_` on a type `X : 𝓤` with values in a universe
`𝓥` (which can of course be `𝓤`) is called an *equivalence relation*
if it is subsingleton-valued, reflexive, symmetric and transitive.
All these notions

\begin{code}
is-subsingleton-valued
 reflexive
 symmetric
 transitive
 is-equivalence-relation :
\end{code}

have the same type

\begin{code}
 {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
\end{code}

and are defined by

\begin{code}
is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)
reflexive               _≈_ = ∀ x → x ≈ x
symmetric               _≈_ = ∀ x y → x ≈ y → y ≈ x
transitive              _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

is-equivalence-relation _≈_ = is-subsingleton-valued _≈_
                            × reflexive _≈_
                            × symmetric _≈_
                            × transitive _≈_
\end{code}

We now work with a submodule with parameters to quotient a given type
`X` by a given equivalence relation `_≈_`. We assume not only the
existence of propositional truncations, as discussed above, but also
functional and propositional extensionality.

\begin{code}
module quotient
       {𝓤 𝓥 : Universe}
       (pt  : subsingleton-truncations-exist)
       (hfe : global-hfunext)
       (pe  : propext 𝓥)
       (X   : 𝓤 ̇ )
       (_≈_ : X → X → 𝓥 ̇ )
       (≈p  : is-subsingleton-valued _≈_)
       (≈r  : reflexive _≈_)
       (≈s  : symmetric _≈_)
       (≈t  : transitive _≈_)
      where

 open basic-truncation-development pt hfe
\end{code}

From the given relation

   > `_≈_ : X → X → 𝓥 ̇`

we define a function

   > `X → (X → Ω 𝓥)`,

and we take the quotient `X/≈` to be the image of this function. It is
for constructing the image that we need subsingleton
truncations. Functional and propositional extensionality are then used
to prove that the quotient is a set.

\begin{code}
 equiv-rel : X → (X → Ω 𝓥)
 equiv-rel x y = (x ≈ y) , ≈p x y

 X/≈ : 𝓥 ⁺ ⊔ 𝓤  ̇
 X/≈ = image equiv-rel

 X/≈-is-set : is-set X/≈
 X/≈-is-set = subsets-of-sets-are-sets (X → Ω 𝓥) _
               (powersets-are-sets (dfunext-gives-hfunext hunapply) hunapply pe)
               (λ _ → ∃-is-subsingleton)

 η : X → X/≈
 η = corestriction equiv-rel
\end{code}

We show that `η` is the universal solution to the problem of transforming
equivalence `_≈_` into equality `_≡_`.

By construction, `η` is a surjection, of course:

\begin{code}
 η-surjection : is-surjection η
 η-surjection = corestriction-surjection equiv-rel
\end{code}

It is convenient to use the following induction principle for
reasoning about the image `X/≈`.

\begin{code}
 η-induction : (P : X/≈ → 𝓦 ̇ )
             → ((x' : X/≈) → is-subsingleton (P x'))
             → ((x : X) → P (η x))
             → (x' : X/≈) → P x'

 η-induction = surjection-induction η η-surjection
\end{code}

The first part of the universal property of `η` says that equivalent
points are mapped to identified points:

\begin{code}
 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e =
  to-Σ-≡
    (hunapply (λ z → to-Σ-≡
                       (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                        being-subsingleton-is-subsingleton hunapply _ _)) ,
     ∃-is-subsingleton _ _)
\end{code}

To prove the required universal property, we also need the fact that
`η` reflects equality into equivalence:

\begin{code}
 η-equal-equiv : {x y : X} → η x ≡ η y → x ≈ y
 η-equal-equiv {x} {y} p = equiv-rel-reflect (ap pr₁ p)
  where
   equiv-rel-reflect : equiv-rel x ≡ equiv-rel y → x ≈ y
   equiv-rel-reflect q = b (≈r y)
    where
     a : (y ≈ y) ≡ (x ≈ y)
     a = ap (λ - → pr₁(- y)) (q ⁻¹)

     b : y ≈ y → x ≈ y
     b = Id→fun a
\end{code}

We are now ready to formulate and prove the required universal
property of the quotient. What is noteworthy here, regarding
universes, is that the universal property says that we can eliminate
into any set `A` of any universe `𝓦`.

\begin{code}
 universal-property : (A : 𝓦 ̇ )
                    → is-set A
                    → (f : X → A)
                    → ({x x' : X} → x ≈ x' → f x ≡ f x')
                    → ∃! \(f' : X/≈ → A) → f' ∘ η ≡ f

 universal-property {𝓦} A i f τ = e
  where
   G : X/≈ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ̇
   G x' = Σ \a → ∃ \x → (η x ≡ x') × (f x ≡ a)

   φ : (x' : X/≈) → is-subsingleton (G x')
   φ = η-induction _ γ induction-step
    where
     induction-step : (y : X) → is-subsingleton (G (η y))
     induction-step x (a , d) (b , e) = to-Σ-≡ (p , ∃-is-subsingleton _ _)
      where
       h : (Σ \x' → (η x' ≡ η x) × (f x' ≡ a))
         → (Σ \y' → (η y' ≡ η x) × (f y' ≡ b))
         → a ≡ b
       h (x' , r , s) (y' , t , u) = a    ≡⟨ s ⁻¹                         ⟩
                                     f x' ≡⟨ τ (η-equal-equiv (r ∙ t ⁻¹)) ⟩
                                     f y' ≡⟨ u                            ⟩
                                     b    ∎

       p : a ≡ b
       p = ∥∥-recursion (i a b) (λ σ → ∥∥-recursion (i a b) (h σ) e) d

     γ : (x' : X/≈) → is-subsingleton (is-subsingleton (G x'))
     γ x' = being-subsingleton-is-subsingleton hunapply

   k : (x' : X/≈) → G x'
   k = η-induction _ φ induction-step
    where
     induction-step : (y : X) → G (η y)
     induction-step x = f x , ∣ x , refl (η x) , refl (f x) ∣

   f' : X/≈ → A
   f' x' = pr₁ (k x')

   r : f' ∘ η ≡ f
   r = hunapply h
    where
     g : (y : X) → ∃ \x → (η x ≡ η y) × (f x ≡ f' (η y))
     g y = pr₂ (k (η y))

     j : (y : X) → (Σ \x → (η x ≡ η y) × (f x ≡ f' (η y))) → f'(η y) ≡ f y
     j y (x , p , q) = f' (η y) ≡⟨ q ⁻¹                ⟩
                       f x      ≡⟨ τ (η-equal-equiv p) ⟩
                       f y      ∎

     h : (y : X) → f'(η y) ≡ f y
     h y = ∥∥-recursion (i (f' (η y)) (f y)) (j y) (g y)

   c : (σ : Σ \(f'' : X/≈ → A) → f'' ∘ η ≡ f) → (f' , r) ≡ σ
   c (f'' , s) = to-Σ-≡ (t , v)
    where
     w : ∀ x → f'(η x) ≡ f''(η x)
     w = happly (f' ∘ η) (f'' ∘ η) (r ∙ s ⁻¹)

     t : f' ≡ f''
     t = hunapply (η-induction _ (λ x' → i (f' x') (f'' x')) w)

     u : f'' ∘ η ≡ f
     u = transport (λ - → - ∘ η ≡ f) t r

     v : u ≡ s
     v = Π-is-set hfe (λ x → i) (f'' ∘ η) f u s

   e : ∃! \(f' : X/≈ → A) → f' ∘ η ≡ f
   e = (f' , r) , c
\end{code}

As mentioned above, if one so wishes, it is possible to resize down
the quotient `X/≈` to the same universe as the given type `X` lives by
assuming propositional resizing. But we don't see any mathematical
need to do so, as the constructed quotient, regardless of the universe
it inhabits, has a universal property that eliminates into any
desired universe, lower, equal or higher than the quotiented type.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="summary"></a> Summary of consistent axioms for univalent mathematics

The following axioms are together consistent by considering Voevodsky's [simplicial-set model](https://arxiv.org/abs/1211.2851):
  1. [Function extensionality](HoTT-UF-Agda.html#hfunext).
  1. [Propositional extensionality](HoTT-UF-Agda.html#propositionalextensionality).
  1. [Univalence](HoTT-UF-Agda.html#univalence).
  1. [Existence of propositional truncations](HoTT-UF-Agda.html#univalence).
  1. [Excluded middle](HoTT-UF-Agda.html#em).
  1. [Choice](HoTT-UF-Agda.html#choice).
  1. [Propositional resizing and impredicativity](HoTT-UF-Agda.html#resizing).

We have that:

  * The first four  admit a constructive interpretation via [cubical
    type theory](https://arxiv.org/abs/1611.02108) with an implementation in [cubical Agda](https://homotopytypetheory.org/2018/12/06/cubical-agda/).

  * Univalence implies [function extensionality](HoTT-UF-Agda.html#funextfromua) and [propositional extensionality](HoTT-UF-Agda.html#propositionalextensionality).

  * Simple unique choice just holds.

  * Full unique choice is equivalent to function extensionality.

  * Choice implies excluded middle, as usual, and both are non-constructive.

  * Excluded middle implies [propositional resizing and impredicativity](HoTT-UF-Agda.html#resizing).

  * The constructive status of propositional resizing and impredicativity is open.

  * Function extensionality and propositional resizing [imply](HoTT-UF-Agda.html#resizing) the existence of propositional truncations, and hence so do function extensionality and excluded middle.

The avoidance of excluded middle and choice makes the theory not only
constructive but also [applicable to more
models](https://arxiv.org/abs/1904.07004). However, one is free to
assume excluded middle and choice for pieces of mathematics that
require them, or just if one simply prefers classical reasoning.

Univalent foundations have enough room for the constructive,
non-constructive, pluralistic and neutral approaches to mathematics,
and in this sense they are no different from e.g. set theoretic
foundations.

A major omission in these notes is a discussion of higher-inductive
types.  On the other hand, these notes completely cover the
foundational principles officially supported by
[UniMath](https://github.com/UniMath/UniMath/blob/master/README.md),
namely (1)-(7) above.

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## <a id="appendix"></a> Appendix

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="someexercisessol"></a> Solutions to some exercises

\begin{code}
module ℕ-order-exercise-solution where

  _≤'_ : ℕ → ℕ → 𝓤₀ ̇
  _≤'_ = ℕ-iteration (ℕ → 𝓤₀ ̇ ) (λ y → 𝟙)
          (λ f → ℕ-recursion (𝓤₀ ̇ ) 𝟘 (λ y P → f y))

  open ℕ-order

  ≤-and-≤'-coincide : (x y : ℕ) → (x ≤ y) ≡ (x ≤' y)
  ≤-and-≤'-coincide 0 y = refl _
  ≤-and-≤'-coincide (succ x) 0 = refl _
  ≤-and-≤'-coincide (succ x) (succ y) = ≤-and-≤'-coincide x y

module ℕ-more where

  open Arithmetic renaming (_+_ to _∔_)
  open basic-arithmetic-and-order

  ≤-prop-valued : (x y : ℕ) → is-subsingleton (x ≤ y)
  ≤-prop-valued 0 y               = 𝟙-is-subsingleton
  ≤-prop-valued (succ x) zero     = 𝟘-is-subsingleton
  ≤-prop-valued (succ x) (succ y) = ≤-prop-valued x y

  ≼-prop-valued : (x y : ℕ) → is-subsingleton (x ≼ y)
  ≼-prop-valued x y (z , p) (z' , p') = to-Σ-≡ (q , r)
   where
    q : z ≡ z'
    q = +-lc x z z' (x ∔ z  ≡⟨ p     ⟩
                     y      ≡⟨ p' ⁻¹ ⟩
                     x ∔ z' ∎)

    r : transport (λ - → x ∔ - ≡ y) q p ≡ p'
    r = ℕ-is-set (x ∔ z') y (transport (λ - → x ∔ - ≡ y) q p) p'

  ≤-charac : propext 𝓤₀ → (x y : ℕ) → (x ≤ y) ≡ (x ≼ y)
  ≤-charac pe x y = pe (≤-prop-valued x y) (≼-prop-valued x y)
                       (≤-gives-≼ x y) (≼-gives-≤ x y)

the-subsingletons-are-the-subtypes-of-a-singleton : (X : 𝓤 ̇ )
                                                  → is-subsingleton X ⇔ (X ↪ 𝟙)
the-subsingletons-are-the-subtypes-of-a-singleton X = φ , ψ
 where
  i : is-subsingleton X → is-embedding (!𝟙' X)
  i s ⋆ (x , refl ⋆) (y , refl ⋆) = ap (λ - → - , refl ⋆) (s x y)

  φ : is-subsingleton X → X ↪ 𝟙
  φ s = !𝟙 , i s

  ψ : X ↪ 𝟙 → is-subsingleton X
  ψ (f , e) x y = d
   where
    a : x ≡ y → f x ≡ f y
    a = ap f {x} {y}

    b : is-equiv a
    b = embedding-gives-ap-is-equiv f e x y

    c : f x ≡ f y
    c = 𝟙-is-subsingleton (f x) (f y)

    d : x ≡ y
    d = inverse a b c

the-subsingletons-are-the-subtypes-of-a-singleton' : propext 𝓤 → global-dfunext
                                                   → (X : 𝓤 ̇ )
                                                   → is-subsingleton X ≡ (X ↪ 𝟙)
the-subsingletons-are-the-subtypes-of-a-singleton' pe fe X = γ
 where
  a : is-subsingleton X ⇔ (X ↪ 𝟙)
  a = the-subsingletons-are-the-subtypes-of-a-singleton X

  b : is-subsingleton (X ↪ 𝟙)
  b (f , e) (f' , e') = to-Σ-≡ (fe (λ x → 𝟙-is-subsingleton (f x) (f' x)) ,
                                being-embedding-is-subsingleton fe f' _ e')

  γ : is-subsingleton X ≡ (X ↪ 𝟙)
  γ = pe (being-subsingleton-is-subsingleton fe) b (pr₁ a) (pr₂ a)

G↑-≃-equation : (ua : is-univalent (𝓤 ⊔ 𝓥))
              → (X : 𝓤 ̇ )
              → (A : (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y) → 𝓦 ̇ )
              → (a : A (Lift 𝓥 X , ≃-Lift X))
              → G↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ≡ a
G↑-≃-equation {𝓤} {𝓥} {𝓦} ua X A a =
  G↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ≡⟨ refl (transport A p a)       ⟩
  transport A p a                     ≡⟨ ap (λ - → transport A - a) q ⟩
  transport A (refl t) a              ≡⟨ refl a                       ⟩
  a                                   ∎
 where
  t : (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
  t = (Lift 𝓥 X , ≃-Lift X)

  p : t ≡ t
  p = univalence→'' {𝓤} {𝓤 ⊔ 𝓥} ua X t t

  q : p ≡ refl t
  q = subsingletons-are-sets (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
       (univalence→'' {𝓤} {𝓤 ⊔ 𝓥} ua X) t t p (refl t)

H↑-≃-equation : (ua : is-univalent (𝓤 ⊔ 𝓥))
              → (X : 𝓤 ̇ )
              → (A : (Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y → 𝓦 ̇ )
              → (a : A (Lift 𝓥 X) (≃-Lift X))
              → H↑-≃ ua X A a (Lift 𝓥 X) (≃-Lift X) ≡ a
H↑-≃-equation ua X A = G↑-≃-equation ua X (Σ-induction A)

has-section-charac : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → ((y : Y) → Σ \(x : X) → f x ≡ y) ≃ has-section f
has-section-charac f = ΠΣ-distr-≃

retractions-into : 𝓤 ̇ → 𝓤 ⁺ ̇
retractions-into {𝓤} Y = Σ \(X : 𝓤 ̇ ) → Y ◁ X

pointed-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
pointed-types 𝓤 = Σ \(X : 𝓤 ̇ ) → X

retraction-classifier : Univalence
                      → (Y : 𝓤 ̇ ) → retractions-into Y ≃ (Y → pointed-types 𝓤)
retraction-classifier {𝓤} ua Y =
 retractions-into Y                                               ≃⟨ i      ⟩
 (Σ \(X : 𝓤 ̇ ) → Σ \(f : X → Y) → (y : Y) → Σ \(x : X) → f x ≡ y) ≃⟨ id-≃ _ ⟩
 ((𝓤 /[ id ] Y))                                                  ≃⟨ ii     ⟩
 (Y → pointed-types 𝓤)                                            ■
 where
  i  = ≃-sym (Σ-cong (λ X → Σ-cong (λ f → ΠΣ-distr-≃)))
  ii = special-map-classifier (ua 𝓤)
        (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
        id Y

module surjection-classifier
         (pt : subsingleton-truncations-exist)
         (ua : Univalence)
       where

  hfe : global-hfunext
  hfe = univalence-gives-global-hfunext ua

  open basic-truncation-development pt hfe public

  _↠_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  X ↠ Y = Σ \(f : X → Y) → is-surjection f

  surjections-into : 𝓤 ̇ → 𝓤 ⁺ ̇
  surjections-into {𝓤} Y = Σ \(X : 𝓤 ̇ ) → X ↠ Y

  inhabited-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
  inhabited-types 𝓤 = Σ \(X : 𝓤 ̇ ) → ∥ X ∥

  surjection-classifier : Univalence
                        → (Y : 𝓤 ̇ )
                        → surjections-into Y ≃ (Y → inhabited-types 𝓤)
  surjection-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                  (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                  ∥_∥
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="moreexercises"></a> Additional exercises

Solutions are available [at the end](#additionalexercisessol).

*Exercise*. A sequence of elements of a type `X` is just a function `ℕ → X`.
 Use [Cantor's diagonal
 argument](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)
 to show in Agda that the type of sequences of natural numbers is
 uncountable. Prove a positive version and then derive a negative
 version from it:

\begin{code}
positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)
\end{code}

*Hint.* It may be helpful to prove that the function `succ` has no
 fixed points, first.

*Exercise*.

\begin{code}
𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
\end{code}

Now we would like to have `(𝟚 ≡ 𝟚) ≡ 𝟚` with univalence, but the
problem is that the type `𝟚 ≡ 𝟚` lives in `𝓤₁` whereas `𝟚` lives in
`𝓤₀` and so, having different types, can't be compared for equality.
But we do have that

\begin{code}
lifttwo : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ≡ 𝟚) ≡ Lift 𝓤₁ 𝟚
\end{code}

*Exercise*. Having decidable equality is a subsingleton type.

*Exercise*. We now discuss alternative formulations of the principle of excluded middle.

\begin{code}
DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → ¬¬ P → P

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
### <a id="additionalexercisessol"></a> Solutions to additional exercises

\begin{code}
succ-no-fixed-point : (n : ℕ) → succ n ≢ n
succ-no-fixed-point 0        = positive-not-zero 0
succ-no-fixed-point (succ n) = γ
 where
  IH : succ n ≢ n
  IH = succ-no-fixed-point n

  γ : succ (succ n) ≢ succ n
  γ p = IH (succ-lc p)

positive-cantors-diagonal = sol
 where
  sol : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n
  sol e = (α , φ)
   where
    α : ℕ → ℕ
    α n = succ(e n n)

    φ : (n : ℕ) → α ≢ e n
    φ n p = succ-no-fixed-point (e n n) q
     where
      q = succ (e n n)  ≡⟨ refl (α n)       ⟩
          α n           ≡⟨ ap (λ - → - n) p ⟩
          e n n         ∎

cantors-diagonal = sol
 where
  sol : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)
  sol (e , γ) = c
   where
    α : ℕ → ℕ
    α = pr₁ (positive-cantors-diagonal e)

    φ : (n : ℕ) → α ≢ e n
    φ = pr₂ (positive-cantors-diagonal e)

    b : Σ \(n : ℕ) → α ≡ e n
    b = γ α

    c : 𝟘
    c = φ (pr₁ b) (pr₂ b)

𝟚-has-𝟚-automorphisms = sol
 where
  sol : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
  sol fe = invertibility-gives-≃ f (g , η , ε)
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
                     (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q    ⟩
                                                     ₀   ≡⟨ p ⁻¹ ⟩
                                                     h ₀ ∎)))

      γ ₀ ₁ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                               (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                                pr₁ (g ₀) ₀     ≡⟨ refl ₀                   ⟩
                                ₀               ≡⟨ p ⁻¹                     ⟩
                                h ₀             ∎)
                               (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                                pr₁ (g ₀) ₁     ≡⟨ refl ₁                   ⟩
                                ₁               ≡⟨ q ⁻¹                     ⟩
                                h ₁             ∎)),
                         being-equiv-is-subsingleton fe fe _ _ e)

      γ ₁ ₀ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                               (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                                pr₁ (g ₁) ₀     ≡⟨ refl ₁                   ⟩
                                ₁               ≡⟨ p ⁻¹                     ⟩
                                h ₀             ∎)
                               (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                                pr₁ (g ₁) ₁     ≡⟨ refl ₀                   ⟩
                                ₀               ≡⟨ q ⁻¹                     ⟩
                                h ₁             ∎)),
                         being-equiv-is-subsingleton fe fe _ _ e)

      γ ₁ ₁ p q = !𝟘 (g (h ₀) ≡ (h , e))
                     (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q    ⟩
                                                     ₁   ≡⟨ p ⁻¹ ⟩
                                                     h ₀ ∎)))

    ε : (n : 𝟚) → f (g n) ≡ n
    ε ₀ = refl ₀
    ε ₁ = refl ₁

lifttwo = sol
 where
  sol : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ≡ 𝟚) ≡ Lift 𝓤₁ 𝟚
  sol ua₀ ua₁ = Eq→Id ua₁ (𝟚 ≡ 𝟚) (Lift 𝓤₁ 𝟚) e
   where
    e = (𝟚 ≡ 𝟚)   ≃⟨ Id→Eq 𝟚 𝟚 , ua₀ 𝟚 𝟚                                  ⟩
        (𝟚 ≃ 𝟚)   ≃⟨ 𝟚-has-𝟚-automorphisms (univalence-gives-dfunext ua₀) ⟩
        𝟚         ≃⟨ ≃-sym (Lift-≃ 𝟚)                                     ⟩
        Lift 𝓤₁ 𝟚 ■

hde-is-subsingleton : dfunext 𝓤 𝓤₀
                    → dfunext 𝓤 𝓤
                    → (X : 𝓤 ̇ )
                    → is-subsingleton (has-decidable-equality X)
hde-is-subsingleton fe₀ fe X h h' = c h h'
 where
  a : (x y : X) → is-subsingleton (decidable (x ≡ y))
  a x y = +-is-subsingleton' fe₀ b
   where
    b : is-subsingleton (x ≡ y)
    b = hedberg h x y

  c : is-subsingleton (has-decidable-equality X)
  c = Π-is-subsingleton fe (λ x → Π-is-subsingleton fe (a x))

ne = sol
 where
  sol : (X : 𝓤 ̇ ) → ¬¬(X + ¬ X)
  sol X = λ (f : ¬(X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM = sol
 where
  sol : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤
  sol fe dne P i = dne (P + ¬ P) (+-is-subsingleton' fe i) (ne P)

EM-gives-DNE = sol
 where
  sol : EM 𝓤 → DNE 𝓤
  sol em P i = γ (em P i)
   where
    γ : P + ¬ P → ¬¬ P → P
    γ (inl p) φ = p
    γ (inr n) φ = !𝟘 P (φ n)

SN-gives-DNE = sol
 where
  sol : SN 𝓤 → DNE 𝓤
  sol {𝓤} sn P i = h
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

DNE-gives-SN = sol
 where
  sol : DNE 𝓤 → SN 𝓤
  sol dne P i = ¬ P , dni P , dne P i
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
### <a id="infixop"></a> Operator fixities and precedences

Without the following list of operator precedences and
associativities (left or right), this agda file doesn't parse and is
rejected by Agda.

\begin{code}

infix   0 _∼_
infixr 50 _,_
infixr 30 _×_
infixr 20 _+_
infixl 70 _∘_
infix   0 _≡_
infix  10 _⇔_
infixl 30 _∙_
infixr  0 _≡⟨_⟩_
infix   1 _∎
infix  40 _⁻¹
infix  10 _◁_
infixr  0 _◁⟨_⟩_
infix   1 _◀
infix  10 _≃_
infixl 30 _●_
infixr  0 _≃⟨_⟩_
infix   1 _■
infix  40 _∈_

\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
