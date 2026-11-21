---
layout: default
title : Universes (Introduction to Univalent Foundations of Mathematics with Agda)
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
## Universes

We define our notation for type universes used in these notes, which
is different from the [standard Agda notation](https://agda.readthedocs.io/en/latest/language/universe-levels.html), but closer to the
standard notation in HoTT/UF.

Readers unfamiliar with Agda should probably try to understand this
only after doing some [MLTT in Agda](HoTT-UF-Agda.html#mlttinagda) and [HoTT/UF in
Agda](HoTT-UF-Agda.html#uminagda).

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Universes where

open import Agda.Primitive public
 renaming
  ( Level to Universe -- We speak of universes rather than of levels.
  ; lzero to 𝓤₀       -- Our first universe is called 𝓤₀
  ; lsuc to _⁺        -- The universe after 𝓤 is 𝓤 ⁺
  ; Setω to 𝓤ω        -- There is a universe 𝓤ω strictly above 𝓤₀, 𝓤₁, ⋯ , 𝓤ₙ, ⋯
  )
 using (_⊔_)          -- Least upper bound of two universes, e.g. 𝓤₀ ⊔ 𝓤₁ is 𝓤₁
\end{code}

The elements of `Universe` are universe names. Given a name `𝓤`, the
universe itself will be written `𝓤 ̇` &nbsp; in these notes, with a
deliberately almost invisible superscript dot.

We actually need to define this notation, because traditionally in
Agda if one uses `ℓ` for a universe level, then `Set ℓ` is the type of
types of level `ℓ`. However, this notation is not good for univalent
foundations, because not all types are sets. Also the terminology
"level" is not good, because the hlevels in univalent type theory
refer to the complexity of equality rather than size.

The following should be the only use of the Agda keyword `Set` in
these notes.

\begin{code}
Type = λ ℓ → Set ℓ

_̇ : (𝓤 : Universe) → Type (𝓤 ⁺)

𝓤 ̇ = Type 𝓤
\end{code}

This says that given the universe level `𝓤`, we get the type universe
`𝓤 ̇`&nbsp;, which lives in the next next type universe universe `𝓤 ⁺`. So
the superscript dot notation is just a (postfix) synonym for (prefix)
`Type`, which is just a synonym for `Set`, which means type in Agda.

We name a few of the initial universes:

\begin{code}
𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺
\end{code}

For notational convenience, we also define:

\begin{code}
_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺
\end{code}

The following is sometimes useful:

\begin{code}
universe-of : {𝓤 : Universe} (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤
\end{code}

Fixities:

\begin{code}
infix  1 _̇
\end{code}

[<sub>Table of contents ⇑</sub>](HoTT-UF-Agda.html#contents)
