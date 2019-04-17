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
[] ++ ys        = ys
(x :: xs) ++ ys = x :: xs ++ ys

infixr 4 _::_
infixr 6 _++_

++assoc : (xs ys zs : List ℕ) → (xs ++ ys) ++ zs
                              ≡ xs ++ (ys ++ zs)
++assoc [] ys zs = refl (ys ++ zs)
++assoc (x :: xs) ys zs = g
 where
  IH : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  IH = ++assoc xs ys zs
  g : (x :: xs ++ ys) ++ zs   ≡ (x :: xs) ++ (ys ++ zs)
  g = (x :: xs ++ ys) ++ zs   ≡⟨ refl _ ⟩
      x :: ((xs ++ ys) ++ zs) ≡⟨ ap (λ ts → x :: ts) IH ⟩
      x :: (xs ++ (ys ++ zs)) ≡⟨ refl _ ⟩
      (x :: xs) ++ (ys ++ zs) ∎

-- \== \< \> \qed
-- ≡⟨ ⟩ ∎

{- Formulate and prove:

(i) 0 + y ≡ y
(ii) succ x + y ≡ y
(iii) x + y ≡ y + x

-}
