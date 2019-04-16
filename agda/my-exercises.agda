{-# OPTIONS --without-K --exact-split --safe #-}

module my-exercises where

open import Universes
open import HoTT-UF-Agda

-- \MCU
-- \^.

module ex1 where

 open Arithmetic renaming (_+_ to _+'_)

 +assoc : (x y z : ℕ) → (x +' y) +' z
                      ≡ x +' (y +' z)
 +assoc x y zero = refl (x +' y)
 +assoc x y (succ z) = g
  where
   IH : (x +' y) +' z ≡ x +' (y +' z)
   IH = +assoc x y z
   p : succ((x +' y) +' z) ≡ succ(x +' (y +' z))
   p = ap succ IH
   g : (x +' y) +' succ z ≡ x +' (y +' succ z)
   g = p

-- \MCU \_0 \^.

data List ℕ : 𝓤₀ ̇ where
 []   : List ℕ
 _::_ : ℕ → List ℕ → List ℕ

_++_ : List ℕ → List ℕ → List ℕ
_++_ = {!!}

++assoc : (xs ys zs : List ℕ) → (xs ++ ys) ++ zs
                              ≡ xs ++ (ys ++ zs)
++assoc = {!!}
