{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where

open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆

data 𝟘 : 𝓤₀ ̇  where

𝟘-induction : (A : 𝟘 → 𝓤 ̇ )
            → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)

ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 10 _+_
  infixl 11 _×_

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

  infixl 0 _+_
  infixl 1 _×_

module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A(inl x))
            → ((y : Y) → A(inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   x : X
   y : Y x

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A(x , y))
            → (z : Σ Y) → A z
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → ((z : Σ Y) → A z)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x

_≡_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≡ y = Id _ x y

J : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
J X A f x x (refl x) = f x

H : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
H x B b x (refl x) = b

J' : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
J' X A f x = H x (A x) (f x)

Js-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ≡ y)
             → J X A f x y p ≡ J' X A f x y p
Js-agreement X A f x x (refl x) = refl (f x)

transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl x) = 𝑖𝑑 (A x)

transportJ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportJ {𝓤} {𝓥} {X} A {x} {y} = J X (λ x y _ → A x → A y) (λ x → 𝑖𝑑 (A x)) x y

nondep-H : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
         → A x → (y : X) → x ≡ y → A y
nondep-H x A = H x (λ y _ → A y)

transportH : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportH A {x} {y} p a = nondep-H x A a y p

transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → (transportH A p ≡ transport A p)
                     × (transportJ A p ≡ transport A p)
transports-agreement A (refl x) = refl (transport A (refl x)) ,
                                  refl (transport A (refl x))

lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p

_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

dni : (A : 𝓤 ̇ ) → A → ¬¬ A
dni A a u = u a

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

tno : (A : 𝓤 ̇ ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)

absurdity³-is-absurdity : {A : 𝓤 ̇ } → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = contrapositive (dni A)
  secondly : ¬ A → ¬¬¬ A
  secondly = dni (¬ A)

_≢_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)

≢-sym : {X : 𝓤 ̇ } {x y : X} → x ≢ y → y ≢ x
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)

Id-to-Fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))

Id-to-Fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-Fun' (refl X) = 𝑖𝑑 X

Id-to-Funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
                 → Id-to-Fun p ≡ Id-to-Fun' p
Id-to-Funs-agree (refl X) = refl (𝑖𝑑 X)

𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = Id-to-Fun p ⋆

₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p

₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()

𝟚-has-decidable-equality : (m n : 𝟚) → (m ≡ n) + (m ≢ n)
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁

inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 q
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘
  q : 𝟙 ≡ 𝟘
  q = ap f p

module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ \(p : ℕ) → (p ≥ n)
                                              × is-prime p
                                              × is-prime (p ∔ 2)

positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙
  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred

ℕ-has-decidable-equality : (x y : ℕ) → (x ≡ y) + (x ≢ y)
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : (x ≡ y) + x ≢ y → (succ x ≡ succ y) + (succ x ≢ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))

module BasicArithmetic where

  open ℕ-order
  open Arithmetic renaming (_+_ to _∔_)

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

  +-assoc' : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc' x y zero     = refl _
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)

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

  _≼_ : ℕ → ℕ → 𝓤₀ ̇
  x ≼ y = Σ \(z : ℕ) → x ∔ z ≡ y

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

is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = 𝟙-induction
                     (λ x → ∀ y → x ≡ y)
                     (𝟙-induction (λ y → ⋆ ≡ y) (refl ⋆))

𝟙-is-subsingleton' : is-subsingleton 𝟙
𝟙-is-subsingleton' ⋆ ⋆  = refl ⋆

is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop        = is-subsingleton
is-truth-value = is-subsingleton

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)

Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X × (X → X → X)

⟨_⟩ : Magma 𝓤 → 𝓤 ̇
⟨ X , i , _·_ ⟩ = X

magma-is-set : (M : Magma 𝓤) → is-set ⟨ M ⟩
magma-is-set (X , i , _·_) = i

magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
magma-operation (X , i , _·_) = _·_

syntax magma-operation M x y = x ·⟨ M ⟩ y

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

⌜_⌝ : {M N : Magma 𝓤} → M ≡ N → ⟨ M ⟩ → ⟨ N ⟩
⌜ p ⌝ = transport ⟨_⟩ p

⌜⌝-is-iso : {M N : Magma 𝓤} (p : M ≡ N) → is-magma-iso M N (⌜ p ⌝)
⌜⌝-is-iso (refl M) = id-is-magma-iso M

_≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
M ≅ₘ N = Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-iso M N f

magma-Id-to-iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
magma-Id-to-iso p = (⌜ p ⌝ , ⌜⌝-is-iso p )

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → X → X → X

left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
left-neutral e _·_ = ∀ x → e · x ≡ x

right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
right-neutral e _·_ = ∀ x → x · e ≡ x

associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z)

Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoid 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X
                        × Σ \(_·_ : X → X → X)
                        → Σ \(e : X)
                        → left-neutral e _·_
                        × right-neutral e _·_
                        × associative _·_

refl-left : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p

∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)

⁻¹-left∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

⁻¹-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)

ap⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ≡ y)
     → (ap f p)⁻¹ ≡ ap f (p ⁻¹)
ap⁻¹ f (refl x) = refl (refl (f x))

ap-id : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
      → ap id p ≡ p
ap-id (refl x) = refl (refl x)

ap-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
       (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

transport∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p
transport∙ A p (refl y) = refl (transport A p)

Nat : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = (x : domain A) → A x → B x

Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y)
                 → τ y ∘ transport A p ≡ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)

NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

transport-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
               (f : X → Y) {x x' : X} (p : x ≡ x') (a : A (f x))
             → transport (A ∘ f) p a ≡ transport A (ap f p) a
transport-ap A f (refl x) a = refl a

data Color : 𝓤₀ ̇  where
 Black White : Color

apd : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : (x : X) → A x) {x y : X}
      (p : x ≡ y) → transport A p (f x) ≡ f y
apd f (refl x) = refl (f x)

to-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
       → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl x , refl a) = refl (x , a)

from-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
         → σ ≡ τ
         → Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ
from-Σ-≡ (refl (x , a)) = (refl x , refl a)

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ \(c : X) → (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ

singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y ⟩
                                             y ∎

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ )
                                     → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = (x , s x)

EM EM' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM  𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X

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

wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'

collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ \(f : X → X) → wconstant f

collapser : (X : 𝓤 ̇ ) → collapsible X → X → X
collapser X (f , w) = f

collapser-wconstancy : (X : 𝓤 ̇ ) (c : collapsible X) → wconstant (collapser X c)
collapser-wconstancy X (f , w) = w

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

Id-collapsible : 𝓤 ̇ → 𝓤 ̇
Id-collapsible X = (x y : X) → collapsible(x ≡ y)

sets-are-Id-collapsible : (X : 𝓤 ̇ ) → is-set X → Id-collapsible X
sets-are-Id-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q

Id-collapsibles-are-sets : (X : 𝓤 ̇ ) → Id-collapsible X → is-set X
Id-collapsibles-are-sets X c x = Hedberg x
                                  (λ y → collapser (x ≡ y) (c x y) ,
                                  collapser-wconstancy (x ≡ y) (c x y))

subsingletons-are-Id-collapsible : (X : 𝓤 ̇ )
                                 → is-subsingleton X
                                 → Id-collapsible X
subsingletons-are-Id-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)

subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = Id-collapsibles-are-sets X
                               (subsingletons-are-Id-collapsible X s)

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

_has-minimal-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X has-minimal-hlevel 0 = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) × ¬(X is-of-hlevel n)

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

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ \(s : codomain r → domain r) → r ∘ s ∼ id

_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ \(r : Y → X) → has-section r

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

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl X = 𝑖𝑑 X , 𝑖𝑑 X , refl

_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
  η'' = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
              r (s x)           ≡⟨ η x ⟩
              x                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = ◁-refl X

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

transport-is-retraction : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                        → transport A p ∘ transport A (p ⁻¹) ∼ 𝑖𝑑 (A y)
transport-is-retraction A (refl x) = refl

transport-is-section : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → transport A (p ⁻¹) ∘ transport A p ∼ 𝑖𝑑 (A x)
transport-is-section A (refl x) = refl

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

retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → Y ◁ X → is-singleton X → is-singleton Y
retract-of-singleton (r , s , η) (c , φ) = r c , γ
 where
  γ = λ y → r c     ≡⟨ ap r (φ (s y)) ⟩
            r (s y) ≡⟨ η y ⟩
            y       ∎

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

invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ \(x : domain f) → f x ≡ y

fiber-point : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
            → fiber f y → X
fiber-point (x , p) = x

fiber-identification : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y}
                     → (w : fiber f y) → f (fiber-point w) ≡ y
fiber-identification (x , p) = p

is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)

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

inverse-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                 → is-equiv (inverse f e)
inverse-is-equiv f e = invertibles-are-equivs
                         (inverse f e)
                         (f , inverse-is-section f e , inverse-is-retraction f e)

inversion-involutive : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                     → inverse (inverse f e) (inverse-is-equiv f e) ≡ f
inversion-involutive f e = refl f

id-invertible : (X : 𝓤 ̇ ) → invertible (𝑖𝑑 X)
id-invertible X = 𝑖𝑑 X , refl , refl

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

id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (𝑖𝑑 X)
id-is-equiv = singleton-types-are-singletons

∘-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
           → is-equiv g → is-equiv f → is-equiv (g ∘ f)
∘-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j = γ
 where
  abstract
   γ : is-equiv (g ∘ f)
   γ = invertibles-are-equivs (g ∘ f)
         (∘-invertible (equivs-are-invertible g i)
         (equivs-are-invertible f j))

inverse-of-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇}
               (f : X → Y) (g : Y → Z)
               (i : is-equiv f) (j : is-equiv g)
             → inverse f i ∘ inverse g j ∼ inverse (g ∘ f) (∘-is-equiv j i)
inverse-of-∘ f g i j z =
  f' (g' z)             ≡⟨ (ap (f' ∘ g') (s z))⁻¹ ⟩
  f' (g' (g (f (h z)))) ≡⟨ ap f' (inverse-is-retraction g j (f (h z))) ⟩
  f' (f (h z))          ≡⟨ inverse-is-retraction f i (h z) ⟩
  h z                   ∎
 where
  f' = inverse f i
  g' = inverse g j
  h = inverse (g ∘ f) (∘-is-equiv j i)
  s : g ∘ f ∘ h ∼ id
  s = inverse-is-section (g ∘ f) (∘-is-equiv j i)

_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

Eq-to-fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq-to-fun (f , i) = f

Eq-to-fun-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (Eq-to-fun e)
Eq-to-fun-is-equiv (f , i) = i

invertibility-gives-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → invertible f → X ≃ Y
invertibility-gives-≃ f i = f , invertibles-are-equivs f i

≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = 𝑖𝑑 X , id-is-equiv X

_●_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverse-is-equiv f e

_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = ≃-refl

transport-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)
transport-is-equiv A (refl x) = id-is-equiv (A x)

Σ-≡-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ τ : Σ A)
      → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
Σ-≡-≃ {𝓤} {𝓥} {X} {A}  σ τ = invertibility-gives-≃ from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
    → from-Σ-≡ (to-Σ-≡ w) ≡ w
  η (refl p , refl q) = refl (refl p , refl q)
  ε : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε (refl σ) = refl (refl σ)

Σ-cong : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B
Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ =
  invertibility-gives-≃ (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε)
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

Id-to-Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id-to-Eq X X (refl X) = ≃-refl X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id-to-Eq X Y)

is-univalent-≃ : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → (X ≡ Y) ≃ (X ≃ Y)
is-univalent-≃ ua X Y = Id-to-Eq X Y , ua X Y

Eq-to-Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq-to-Id ua X Y = inverse (Id-to-Eq X Y) (ua X Y)

Id-to-fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-fun {𝓤} {X} {Y} p = Eq-to-fun (Id-to-Eq X Y p)

Id-to-funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
                 → Id-to-fun p ≡ Id-to-Fun p
Id-to-funs-agree (refl X) = refl (𝑖𝑑 X)

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

module example-of-a-nonset (ua : is-univalent 𝓤₀) where

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

 𝓤₀-is-not-a-set : ¬(is-set (𝓤₀ ̇ ))
 𝓤₀-is-not-a-set s = p₀-is-not-p₁ q
  where
   q : p₀ ≡ p₁
   q = s 𝟚 𝟚 p₀ p₁

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

is-joyal-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f

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

pr₁-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
       → ((x : X) → is-subsingleton (A x))
       → left-cancellable  (λ (t : Σ A) → pr₁ t)

subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                         → is-set X
                         → ((x : X) → is-subsingleton(A x))
                         → is-set(Σ \(x : X) → A x)

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

subsingleton-criterion = sol
 where
  sol : {X : 𝓤 ̇ } → (X → is-singleton X) → is-subsingleton X
  sol f x = singletons-are-subsingletons (domain f) (f x) x

lc-maps-reflect-subsingletons = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → left-cancellable f → is-subsingleton Y → is-subsingleton X
  sol f l s x x' = l (s (f x) (f x'))

sections-are-lc = sol
 where
  sol : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A)
      → has-retraction s → left-cancellable s
  sol s (r , ε) {x} {y} p = x ≡⟨ (ε x)⁻¹ ⟩
                            r (s x) ≡⟨ ap r p ⟩
                            r (s y) ≡⟨ ε y ⟩
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
   f' (g' z)                          ≡⟨ h (g' z) ⟩
   inverse f i (g' z)                 ≡⟨ ap (inverse f i) (k z) ⟩
   inverse f i (inverse g j z)        ≡⟨ inverse-of-∘ f g i j z ⟩
   inverse (g ∘ f) (∘-is-equiv j i) z ∎

equiv-to-set = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → is-set Y → is-set X
  sol e = subtypes-of-sets-are-sets
            (Eq-to-fun e)
            (equivs-are-lc (Eq-to-fun e) (Eq-to-fun-is-equiv e))

sections-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → has-retraction f → g ∼ f → has-retraction g
  sol f g (r , rf) h = (r ,
                        λ x → r (g x) ≡⟨ ap r (h x) ⟩
                              r (f x) ≡⟨ rf x ⟩
                              x       ∎)

retractions-closed-under-∼ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → has-section f → g ∼ f → has-section g
  sol f g (s , fs) h = (s ,
                        λ y → g (s y) ≡⟨ h (s y) ⟩
                              f (s y) ≡⟨ fs y ⟩
                              y ∎)

one-inverse = sol
 where
  sol : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
        (f : X → Y) (r s : Y → X)
      → (r ∘ f ∼ id)
      → (f ∘ s ∼ id)
      → r ∼ s
  sol X Y f r s h k y = r y         ≡⟨ ap r ((k y)⁻¹) ⟩
                        r (f (s y)) ≡⟨ h (s y) ⟩
                        s y         ∎

joyal-equivs-are-invertible = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
      → is-joyal-equiv f → invertible f
  sol f ((s , ε) , (r , η)) = (s , sf , ε)
   where
    sf = λ (x : domain f) → s(f x)       ≡⟨ (η (s (f x)))⁻¹ ⟩
                            r(f(s(f x))) ≡⟨ ap r (ε (f x)) ⟩
                            r(f x)       ≡⟨ η x ⟩
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
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → is-equiv f → g ∼ f → is-equiv g
  sol f g e h = joyal-equivs-are-equivs g
                 (retractions-closed-under-∼ f g
                   (equivs-have-sections f e) h ,
                  sections-closed-under-∼ f g
                   (equivs-have-retractions f e) h)

equivs-closed-under-∼' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
      → is-equiv f → f ∼ g → is-equiv g
  sol f g e h = equivs-closed-under-∼ f g e (λ x → (h x)⁻¹)

equiv-to-singleton' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → X ≃ Y → is-singleton X → is-singleton Y
  sol e = retract-of-singleton (≃-gives-▷ e)

subtypes-of-sets-are-sets = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
      → left-cancellable m → is-set Y → is-set X
  sol {𝓤} {𝓥} {X} m i h = Id-collapsibles-are-sets X c
   where
    f : (x x' : X) → x ≡ x' → x ≡ x'
    f x x' r = i (ap m r)
    κ : (x x' : X) (r s : x ≡ x') → f x x' r ≡ f x x' s
    κ x x' r s = ap i (h (m x) (m x') (ap m r) (ap m s))
    c : Id-collapsible X
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
     → ((x : X) → is-subsingleton(A x))
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

×-is-subsingleton = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → is-subsingleton X → is-subsingleton Y → is-subsingleton (X × Y)
  sol i j = Σ-is-subsingleton i (λ _ → j)

to-×-≡ = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {z t : X × Y}
      → pr₁ z ≡ pr₁ t → pr₂ z ≡ pr₂ t → z ≡ t
  sol (refl x) (refl y) = refl (x , y)

×-is-subsingleton' = sol
 where
  sol : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
      → ((Y → is-subsingleton X) × (X → is-subsingleton Y))
      → is-subsingleton (X × Y)
  sol {𝓤} {𝓥} {X} {Y} (i , j) = k
   where
    k : is-subsingleton (X × Y)
    k (x , y) (x' , y') = to-×-≡ (i y x x') (j x y y')

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

univalence→ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)
univalence→ ua X = equiv-subsingleton-lemma X (Id-to-Eq X) (ua X)

→univalence : ((X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y))
            → is-univalent 𝓤
→univalence i X = subsingleton-equiv-lemma X (Id-to-Eq X) (i X)

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

J-≃ : is-univalent 𝓤
    → (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → ((X : 𝓤 ̇ ) → A X X (≃-refl X))
    → (X Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e
J-≃ ua A φ X = H-≃ ua X (A X) (φ X)

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

J-equiv : is-univalent 𝓤
        → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
        → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
        → (X Y : 𝓤 ̇ ) (f : X → Y) → is-equiv f → A X Y f
J-equiv ua A φ X = H-equiv ua X (A X) (φ X)

J-invertible : is-univalent 𝓤
             → (A : (X Y : 𝓤 ̇ ) → (X → Y) → 𝓥 ̇ )
             → ((X : 𝓤 ̇ ) → A X X (𝑖𝑑 X))
             → (X Y : 𝓤 ̇ ) (f : X → Y) → invertible f → A X Y f
J-invertible ua A φ X Y f i = J-equiv ua A φ X Y f (invertibles-are-equivs f i)

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

Σ-change-of-variables : is-univalent 𝓤
                      → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : Y → 𝓥 ̇ ) (f : X → Y)
                      → is-equiv f
                      → (Σ \(y : Y) → A y) ≡ (Σ \(x : X) → A (f x))
Σ-change-of-variables ua A f i = Σ-change-of-variables' ua A
                                    (inverse f i)
                                    (inverse-is-equiv f i)

transport-map-along-≡ : {X Y Z : 𝓤 ̇ } (p : X ≡ Y) (g : X → Z)
                      → transport (λ - → - → Z) p g
                      ≡ g ∘ Id-to-fun (p ⁻¹)
transport-map-along-≡ (refl X) = refl

transport-map-along-≃ : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ }
                        (e : X ≃ Y) (g : X → Z)
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

is-hae : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-hae f = Σ \(g : codomain f → domain f)
         → Σ \(η : g ∘ f ∼ id)
         → Σ \(ε : f ∘ g ∼ id)
         → (x : domain f) → ap f (η x) ≡ ε (f x)

haes-are-invertible : {X Y : 𝓤 ̇ } (f : X → Y)
                    → is-hae f → invertible f
haes-are-invertible f (g , η , ε , τ) = g , η , ε

haes-are-equivs : {X Y : 𝓤 ̇ } (f : X → Y)
                → is-hae f → is-equiv f
haes-are-equivs f i = invertibles-are-equivs f (haes-are-invertible f i)

id-is-hae : (X : 𝓤 ̇ ) → is-hae (𝑖𝑑 X)
id-is-hae X = 𝑖𝑑 X , refl , refl , (λ x → refl (refl x))

equivs-are-haes : is-univalent 𝓤
                → {X Y : 𝓤 ̇ } (f : X → Y)
                → is-equiv f → is-hae f
equivs-are-haes ua {X} {Y} = J-equiv ua (λ X Y f → is-hae f) id-is-hae X Y

ua-invertibles-are-haes : is-univalent 𝓤
                        → {X Y : 𝓤 ̇ } (f : X → Y)
                        → invertible f → is-hae f
ua-invertibles-are-haes ua f i = equivs-are-haes ua f (invertibles-are-equivs f i)

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
   η (h x) ∙ refl (h x)            ≡⟨ i ⟩
   η (h x) ∙ (η x ∙ (η x)⁻¹)       ≡⟨ ii ⟩
   η (h x) ∙ η x ∙ (η x)⁻¹         ≡⟨ iii ⟩
   η (h x) ∙ ap id (η x) ∙ (η x)⁻¹ ≡⟨ iv ⟩
   ap h (η x)                      ∎
 where
  i   = ap (λ - → η(h x) ∙ -) ((⁻¹-right∙ (η x))⁻¹)
  ii  = (∙assoc (η (h x)) (η x) (η x ⁻¹))⁻¹
  iii = ap (λ - → η (h x) ∙ - ∙ η x ⁻¹) ((ap-id (η x))⁻¹)
  iv  = ~-naturality' h id η {h x} {x} {η x}

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
       ap (g ∘ f) (η x)  ≡⟨ ap-∘ f g (η x) ⟩
       ap g (ap f (η x)) ∎

   q = ap f (η (g (f x))) ∙ ε (f x)         ≡⟨ i ⟩
       ap f (ap g (ap f (η x))) ∙ ε (f x)   ≡⟨ ii ⟩
       ap (f ∘ g) (ap f (η x)) ∙ ε (f x)    ≡⟨ iii ⟩
       ε (f (g (f x))) ∙ ap id (ap f (η x)) ≡⟨ iv ⟩
       ε (f (g (f x))) ∙ ap f (η x)         ∎
    where
     i   = ap (λ - → - ∙ ε (f x)) (ap (ap f) p)
     ii  = ap (λ - → - ∙ ε (f x)) ((ap-∘ g f (ap f (η x)))⁻¹)
     iii = (~-naturality (f ∘ g) id ε {f (g (f x))} {f x} {ap f (η x)})⁻¹
     iv  = ap (λ - → ε (f (g (f x))) ∙ -) ((ap-∘ f id (η x))⁻¹)

   τ = ap f (η x)                                           ≡⟨ refl-left ⁻¹ ⟩
       refl (f (g (f x))) ∙ ap f (η x)                      ≡⟨ i ⟩
       (ε (f (g (f x))))⁻¹ ∙ ε (f (g (f x))) ∙ ap f (η x)   ≡⟨ ii ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ε (f (g (f x))) ∙ ap f (η x)) ≡⟨ iii ⟩
       (ε (f (g (f x))))⁻¹ ∙ (ap f (η (g (f x))) ∙ ε (f x)) ≡⟨ refl _ ⟩
       ε' (f x)                                             ∎
    where
     i   = ap (λ - → - ∙ ap f (η x)) ((⁻¹-left∙ (ε (f (g (f x)))))⁻¹)
     ii  = ∙assoc ((ε (f (g (f x))))⁻¹) (ε (f (g (f x)))) (ap f (η x))
     iii = ap (λ - → (ε (f (g (f x))))⁻¹ ∙ -) (q ⁻¹)

Σ-change-of-variables-hae : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ ) (f : X → Y)
                          → is-hae f → Σ A ≃ Σ (A ∘ f)
Σ-change-of-variables-hae A f (g , η , ε , τ) = γ
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

    q = transport (A ∘ f) (η x)  b ≡⟨ transport-ap A f (η x) b ⟩
        transport A (ap f (η x)) b ≡⟨ ap (λ - → transport A - b) (τ x) ⟩
        transport A (ε (f x))    b ≡⟨ transport-is-retraction A (ε (f x)) a ⟩
        a                          ∎
  γ : Σ A ≃ Σ (A ∘ f)
  γ = invertibility-gives-≃ φ (ψ , ψφ , φψ)

funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g

pre-comp-is-equiv : is-univalent 𝓤
                  → (X Y : 𝓤 ̇ ) (f : X → Y)
                  → is-equiv f
                  → (Z : 𝓤 ̇ ) → is-equiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv {𝓤} ua =
   J-equiv ua
     (λ X Y (f : X → Y) → (Z : 𝓤 ̇ ) → is-equiv (λ g → g ∘ f))
     (λ X Z → id-is-equiv (X → Z))

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

  γ' : f₀ ∼ f₁ → f₀ ≡ f₁
  γ' h = f₀                             ≡⟨ refl _ ⟩
         (λ x → f₀ x)                   ≡⟨ refl _ ⟩
         (λ x → π₀ (f₀ x , f₁ x , h x)) ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) q ⟩
         (λ x → π₁ (f₀ x , f₁ x , h x)) ≡⟨ refl _ ⟩
         (λ x → f₁ x)                   ≡⟨ refl _ ⟩
         f₁                             ∎

dfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g

happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

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

post-comp-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                     → funext 𝓦 𝓤 → funext 𝓦 𝓥
                     → (f : X → Y)
                     → invertible f
                     → invertible (λ (h : A → X) → f ∘ h)
post-comp-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = γ
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)
  γ : invertible (λ h → f ∘ h)
  γ = (g' , η' , ε')

post-comp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                   → funext 𝓦 𝓤 → funext 𝓦 𝓥
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

funext-gives-vvfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → vvfunext 𝓤 𝓥
funext-gives-vvfunext {𝓤} {𝓥} fe fe' {X} {A} φ = γ
 where
  f : Σ A → X
  f = pr₁
  f-is-equiv : is-equiv f
  f-is-equiv = pr₁-equiv φ
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

funext-gives-hfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → hfunext 𝓤 𝓥
dfunext-gives-hfunext      : dfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
funext-gives-dfunext       : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → dfunext 𝓤 𝓥
univalence-gives-dfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
univalence-gives-hfunext'  : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → hfunext 𝓤 𝓥
univalence-gives-vvfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → vvfunext 𝓤 𝓥
univalence-gives-hfunext   : is-univalent 𝓤 → hfunext 𝓤 𝓤
univalence-gives-dfunext   : is-univalent 𝓤 → dfunext 𝓤 𝓤
univalence-gives-vvfunext  : is-univalent 𝓤 → vvfunext 𝓤 𝓤

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

_/_ : (𝓤 : Universe) → 𝓤 ̇ → 𝓤 ⁺ ̇
𝓤 / Y = Σ \(X : 𝓤 ̇ ) → X → Y

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

χ : (Y : 𝓤 ̇ ) → 𝓤 / Y  → (Y → 𝓤 ̇ )
χ Y (X , f) = fiber f

is-map-classifier : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-map-classifier 𝓤 = (Y : 𝓤 ̇ ) → is-equiv (χ Y)

T : (Y : 𝓤 ̇ ) → (Y → 𝓤 ̇ ) → 𝓤 / Y
T Y A = Σ A , pr₁

χη : is-univalent 𝓤
   → (Y : 𝓤 ̇ ) → (σ : 𝓤 / Y) → T Y (χ Y σ) ≡ σ
χη ua Y (X , f) = r
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

χε : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
   → (Y : 𝓤 ̇ ) (A : Y → 𝓤 ̇ ) → χ Y (T Y A) ≡ A
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
  γ y = Eq-to-Id ua _ _ (invertibility-gives-≃ (f y) (g y , η y , ε y))

universes-are-map-classifiers : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                              → is-map-classifier 𝓤
universes-are-map-classifiers ua fe Y = invertibles-are-equivs (χ Y)
                                         (T Y , χη ua Y , χε ua fe Y)

map-classification : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                   → (Y : 𝓤 ̇ ) → 𝓤 / Y ≃ (Y → 𝓤 ̇ )
map-classification ua fe Y = χ Y , universes-are-map-classifiers ua fe Y

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
being-equiv-is-a-subsingleton fe fe' f =
 Π-is-subsingleton fe
  (λ x → being-singleton-is-a-subsingleton fe')

univalence-is-a-subsingleton : is-univalent (𝓤 ⁺)
                             → is-subsingleton (is-univalent 𝓤)
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

Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-a-subsingletonω : Univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingletonω {𝓤} γ = univalence-is-a-subsingleton (γ (𝓤 ⁺))

univalence-is-a-singleton : Univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-singleton {𝓤} γ = pointed-subsingletons-are-singletons
                                   (is-univalent 𝓤)
                                   (γ 𝓤)
                                   (univalence-is-a-subsingletonω γ)

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

Π-is-set : hfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = hfunext-gives-dfunext hfe ((λ x → s x (f x) (g x) (p x) (q x)))
  b : is-subsingleton(f ≡ g)
  b = equiv-to-subsingleton (happly f g , hfe f g) a

being-set-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ }
                            → is-subsingleton (is-set X)
being-set-is-a-subsingleton fe =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
       (λ y → being-subsingleton-is-a-subsingleton fe))

hlevel-relation-is-a-subsingleton : dfunext 𝓤 𝓤
                                  → (n : ℕ) (X : 𝓤 ̇ )
                                  → is-subsingleton (X is-of-hlevel n)
hlevel-relation-is-a-subsingleton {𝓤} fe zero X =
 being-singleton-is-a-subsingleton fe
hlevel-relation-is-a-subsingleton fe (succ n) X =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
          (λ x' → hlevel-relation-is-a-subsingleton fe n (x ≡ x')))

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
≃-sym-involutive fe fe' (f , a) = to-Σ-≡
                                   (inversion-involutive f a ,
                                    being-equiv-is-a-subsingleton fe fe' f _ _)

≃-sym-is-equiv : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
               → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-equiv (≃-sym {𝓤} {𝓥} {X} {Y})
≃-sym-is-equiv fe₀ fe₁ fe₂ = invertibles-are-equivs ≃-sym
                                (≃-sym ,
                                 ≃-sym-involutive fe₀ fe₂ ,
                                 ≃-sym-involutive fe₁ fe₂)

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
  FG : (γ : ((x : X) → Y' x)) → F(G γ) ≡ γ
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
                                    → (f : X → Y)
                                    → is-subsingleton (is-joyal-equiv f)

being-joyal-equiv-is-a-subsingleton fe₀ fe₁ fe₂ f =
 ×-is-subsingleton'
  (at-most-one-section fe₂ fe₁ f ,
   at-most-one-retraction fe₀ fe₂ f)

propext : ∀ 𝓤  → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

global-propext : 𝓤ω
global-propext = ∀ {𝓤} → propext 𝓤

univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g =
 Eq-to-Id ua P Q
  (logically-equivalent-subsingletons-are-equivalent P Q i j (f , g))

Id-from-subsingleton : propext 𝓤 → dfunext 𝓤 𝓤
                     → (P : 𝓤 ̇ )
                     → is-subsingleton P
                     → (X : 𝓤 ̇ ) → is-subsingleton (P ≡ X)
Id-from-subsingleton {𝓤} pe fe P i = Hedberg P (λ X → h X , k X)
 where
  module _ (X : 𝓤 ̇ ) where
   f : P ≡ X → is-subsingleton X × (P ⇔ X)
   f p = transport is-subsingleton p i , Id-to-fun p , (Id-to-fun (p ⁻¹))
   g : is-subsingleton X × (P ⇔ X) → P ≡ X
   g (l , φ , ψ) = pe i l φ ψ
   h : P ≡ X → P ≡ X
   h = g ∘ f
   j : is-subsingleton (is-subsingleton X × (P ⇔ X))
   j = ×-is-subsingleton'
        ((λ (_ : P ⇔ X) → being-subsingleton-is-a-subsingleton fe) ,
        (λ (l : is-subsingleton X) → ×-is-subsingleton
                                      (Π-is-subsingleton fe (λ p → l))
                                      (Π-is-subsingleton fe (λ x → i))))
   k : wconstant h
   k p q = ap g (j (f p) (f q))

subsingleton-univalence : propext 𝓤 → dfunext 𝓤 𝓤
                        → (P : 𝓤 ̇ )
                        → is-subsingleton P
                        → (X : 𝓤 ̇ ) → is-equiv (Id-to-Eq P X)
subsingleton-univalence {𝓤} pe fe P i X = γ
 where
  l : P ≃ X → is-subsingleton X
  l e = equiv-to-subsingleton (≃-sym e) i
  eqtoid : P ≃ X → P ≡ X
  eqtoid e = pe i (equiv-to-subsingleton (≃-sym e) i)
                (Eq-to-fun e) (Eq-to-fun (≃-sym e))
  m : is-subsingleton (P ≃ X)
  m (f , k) (f' , k') = to-Σ-≡ (fe (λ x → j (f x) (f' x)) ,
                                being-equiv-is-a-subsingleton fe fe f' _ k')
    where
     j : is-subsingleton X
     j = equiv-to-subsingleton (≃-sym (f , k)) i
  ε : (e : P ≃ X) → Id-to-Eq P X (eqtoid e) ≡ e
  ε e = m (Id-to-Eq P X (eqtoid e)) e
  η : (q : P ≡ X) → eqtoid (Id-to-Eq P X q) ≡ q
  η q = Id-from-subsingleton pe fe P i X (eqtoid (Id-to-Eq P X q)) q
  γ : is-equiv (Id-to-Eq P X)
  γ = invertibles-are-equivs (Id-to-Eq P X) (eqtoid , η , ε)

subsingleton-univalence-≃ : propext 𝓤 → dfunext 𝓤 𝓤
                          → (X P : 𝓤 ̇ ) → is-subsingleton P → (P ≡ X) ≃ (P ≃ X)
subsingleton-univalence-≃ pe fe X P i = Id-to-Eq P X ,
                                        subsingleton-univalence pe fe P i X

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
         being-subsingleton-is-a-subsingleton fe _ _)

Ω-is-a-set : dfunext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-a-set {𝓤} fe pe = Id-collapsibles-are-sets (Ω 𝓤) c
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)
  i : (p q : Ω 𝓤) → is-subsingleton(A p q)
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
    u = Id-to-fun a
    v : q holds → p holds
    v = Id-to-fun (a ⁻¹)
  h : (p q : Ω 𝓤) → A p q → p ≡ q
  h p q (u , v) = Ω-ext fe pe u v
  f : (p q : Ω 𝓤) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  k : (p q : Ω 𝓤) (d e : p ≡ q) → f p q d ≡ f p q e
  k p q d e = ap (h p q) (i p q (g p q d) (g p q e))
  c : (p q : Ω 𝓤) → Σ \(f : p ≡ q → p ≡ q) → wconstant f
  c p q = (f p q , k p q)

powersets-are-sets : hfunext 𝓤 (𝓥 ⁺) → dfunext 𝓥 𝓥 → propext 𝓥
                   → {X : 𝓤 ̇ } → is-set (X → Ω 𝓥)
powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-a-set fe' pe)

𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓤 ̇
x ∈ A = A x holds

_⊆_ : {X : 𝓤 ̇ } → 𝓟 X → 𝓟 X → 𝓤 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 X) → A ⊆ A
⊆-refl A x = 𝑖𝑑 (x ∈ A)

⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence {X} A A (refl A) = ⊆-refl A , ⊆-refl A

subset-extensionality : propext 𝓤 → dfunext 𝓤 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } (A B : 𝓟 X)
                      → A ⊆ B → B ⊆ A → A ≡ B
subset-extensionality pe fe fe' {X} A B h k = fe' φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-Σ-≡ (pe (holds-is-subsingleton (A x))
                   (holds-is-subsingleton (B x)) (h x) (k x) ,
                being-subsingleton-is-a-subsingleton fe
                   (holds-is-subsingleton _)
                   (holds-is-subsingleton _))

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } (A B : 𝓟 X)
                       → A ⊆ B → B ⊆ A → A ≡ B
subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-dfunext (ua 𝓤))
                                 (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))

≃-refl-left : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
            → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
            → ≃-refl X ● α ≡ α
≃-refl-left fe fe' α = to-Σ-≡
                        (refl _ ,
                         being-equiv-is-a-subsingleton fe fe' _ _ _)

≃-sym-left-inverse : dfunext 𝓥 𝓥
                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                   → ≃-sym α ● α ≡ ≃-refl Y
≃-sym-left-inverse fe (f , e) = to-Σ-≡
                                 (p ,
                                  being-equiv-is-a-subsingleton fe fe _ _ _)
 where
  p : f ∘ inverse f e ≡ id
  p = fe (inverse-is-section f e)

≃-sym-right-inverse : dfunext 𝓤 𝓤
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                    → α ● ≃-sym α ≡ ≃-refl X
≃-sym-right-inverse fe (f , e) = to-Σ-≡
                                  (p ,
                                   being-equiv-is-a-subsingleton fe fe _ _ _)
 where
  p : inverse f e ∘ f ≡ id
  p = fe (inverse-is-retraction f e)

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
  p = λ β → ≃-sym α ● (α ● β) ≡⟨ ●-assoc fe₀ fe₁ (≃-sym α) α β ⟩
            (≃-sym α ● α) ● β ≡⟨ ap (_● β) (≃-sym-left-inverse fe₂ α) ⟩
            ≃-refl _ ● β      ≡⟨ ≃-refl-left fe₀ fe₁ _ ⟩
            β                 ∎

  q = λ γ → α ● (≃-sym α ● γ) ≡⟨ ●-assoc fe₃ fe₄ α (≃-sym α) γ ⟩
            (α ● ≃-sym α) ● γ ≡⟨ ap (_● γ) (≃-sym-right-inverse fe₅ α) ⟩
            ≃-refl _ ● γ      ≡⟨ ≃-refl-left fe₃ fe₄ _ ⟩
            γ                 ∎

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

Eq-Eq-cong : global-dfunext
           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
           → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)
Eq-Eq-cong fe = Eq-Eq-cong' fe fe fe fe fe fe fe fe fe fe fe fe

is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = (y : codomain f) → is-subsingleton(fiber f y)

being-embedding-is-a-subsingleton : global-dfunext
                                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-subsingleton(is-embedding f)
being-embedding-is-a-subsingleton fe f =
 Π-is-subsingleton fe
  (λ x → being-subsingleton-is-a-subsingleton fe)

pr₂-embedding : (A : 𝓤 ̇ ) (X : 𝓥 ̇ )
              → is-subsingleton A → is-embedding (λ (z : A × X) → pr₂ z)
pr₂-embedding A X i x ((a , x) , refl x) ((b , x) , refl x) = p
 where
  p : ((a , x) , refl x) ≡ ((b , x) , refl x)
  p = ap (λ - → ((- , x) , refl x)) (i a b)

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
embedding-criterion-converse f e x' x = ≃-sym
                                         (ap f {x'} {x} ,
                                          embedding-gives-ap-is-equiv f e x' x)

_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ \(f : X → Y) → is-embedding f

𝓨 : {X : 𝓤 ̇ } → X → (X → 𝓤 ̇ )
𝓨 {𝓤} {X} = Id X

transport-lemma : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
                → (τ : Nat (𝓨 x) A)
                → (y : X) (p : x ≡ y) → τ y p ≡ transport A p (τ x (refl x))
transport-lemma A x τ x (refl x) = refl (τ x (refl x))

𝓔 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
  → Nat (𝓨 x) A → A x
𝓔 A x τ = τ x (refl x)

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

is-fiberwise-equiv : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                   → Nat A B → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
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

Yoneda-Lemma : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
             → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
             → Nat (𝓨 x) A ≃ A x
Yoneda-Lemma fe fe' A x = 𝓔 A x , 𝓔-is-equiv fe fe' A x

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

_≃̇_ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ≃̇ B = ∀ x → A x ≃ B x

is-representable : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
is-representable A = Σ \(x : domain A) → 𝓨 x ≃̇ A

representable-universal : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                        → is-representable A
                        → is-singleton (Σ A)
representable-universal A (x , e) = retract-universal-lemma A x
                                     (λ x → ≃-gives-▷ (e x))

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

being-fiberwise-equiv-is-a-subsingleton : global-dfunext
                                        → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                                        → (τ : Nat A B)
                                        → is-subsingleton (is-fiberwise-equiv τ)
being-fiberwise-equiv-is-a-subsingleton fe τ =
 Π-is-subsingleton fe
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
        (Σ \(τ : Nat (𝓨 x) A) → is-fiberwise-equiv τ) ≃⟨ pr₁-≃ (i x) ⟩
        Nat (𝓨 x) A                                   ≃⟨ Yoneda-Lemma fe fe A x ⟩
        A x                                           ■
  δ : is-representable A ≃ Σ A
  δ = Σ-cong ε
  v : is-singleton (is-representable A)
  v = equiv-to-singleton δ u
  γ : r₀ ≡ r₁
  γ = singletons-are-subsingletons (is-representable A) v r₀ r₁

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
                                                   (λ y → is-univalent-≃ (ua 𝓤)
                                                           (𝓨 x y) (A y)) ⟩
                    ((y : X) → 𝓨 x y ≃ A y)   ■)
  γ : is-subsingleton (fiber 𝓨 A)
  γ = equiv-to-subsingleton e (being-representable-is-a-subsingleton dfe A)

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
            (f X ≃ f X')  ≃⟨ Eq-Eq-cong' fe fe fe fe fe fe₀ fe₁ fe fe₀ fe₀ fe₀ fe₀
                              (i X) (i X') ⟩
            (X ≃ X')      ≃⟨ ≃-sym (is-univalent-≃ ua X X') ⟩
            (X ≡ X')      ■

Lift-is-embedding : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥)
                  → is-embedding (Lift {𝓤} 𝓥)
Lift-is-embedding {𝓤} {𝓥} ua ua' = universe-embedding-criterion {𝓤} {𝓥} ua ua'
                                    (Lift 𝓥) Lift-≃

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
     e Y = (X ≃ Y)                 ≃⟨ ≃-Sym fe₀ fe₁ fe ⟩
           (Y ≃ X)                 ≃⟨ Eq-Eq-cong' fe₁ fe fe₂ fe₁ fe fe fe fe₃ fe
                                       fe fe fe (≃-Lift Y) (≃-Lift X) ⟩
           (Lift 𝓤 Y ≃ Lift 𝓥 X)  ≃⟨ ≃-sym (is-univalent-≃ ua'
                                             (Lift 𝓤 Y) (Lift 𝓥 X)) ⟩
           (Lift 𝓤 Y ≡ Lift 𝓥 X)  ■
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

univalence→'' : is-univalent (𝓤 ⊔ 𝓥) → (X : 𝓤 ̇ )
              → is-subsingleton (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
univalence→'' ua = univalence→' ua ua

univalence→''-dual : is-univalent (𝓤 ⊔ 𝓥) → (Y : 𝓤 ̇ )
                   → is-subsingleton (Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)
univalence→''-dual ua = univalence→'-dual ua ua

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

J↑-invertible : is-univalent (𝓤 ⊔ 𝓥)
              → (A : (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) → (X → Y) → 𝓦 ̇ )
              → ((X : 𝓤 ̇ ) → A X (Lift 𝓥 X) lift)
              → (X : 𝓤 ̇ ) (Y : 𝓤 ⊔ 𝓥 ̇ ) (f : X → Y) → invertible f → A X Y f
J↑-invertible ua A φ X Y f i = J↑-equiv ua A φ X Y f (invertibles-are-equivs f i)

lift-is-hae : (X : 𝓤 ̇ ) → is-hae {𝓤} {𝓤 ⊔ 𝓥} {X} {Lift 𝓥 X} (lift {𝓤} {𝓥})
lift-is-hae {𝓤} {𝓥} X = lower ,
                        lower-lift {𝓤} {𝓥} ,
                        lift-lower ,
                        λ x → refl (refl (lift x))

equivs-are-haes↑ : is-univalent (𝓤 ⊔ 𝓥)
                 → {X : 𝓤 ̇ } {Y : 𝓤 ⊔ 𝓥 ̇ } (f : X → Y)
                 → is-equiv f → is-hae f
equivs-are-haes↑ {𝓤} {𝓥} ua {X} {Y} = J↑-equiv {𝓤} {𝓥} ua (λ X Y f → is-hae f)
                                       lift-is-hae X Y

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

J↓-invertible : is-univalent (𝓤 ⊔ 𝓥)
              → (A : (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) → (X → Y) → 𝓦 ̇ )
              → ((Y : 𝓤 ̇ ) → A (Lift 𝓥 Y) Y lower)
              → (X : 𝓤 ⊔ 𝓥 ̇ ) (Y : 𝓤 ̇ ) (f : X → Y) → invertible f → A X Y f
J↓-invertible ua A φ X Y f i = J↓-equiv ua A φ X Y f (invertibles-are-equivs f i)

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

Id-to-Eq-is-hae : is-univalent 𝓤 → is-univalent (𝓤 ⁺)
                → {X Y : 𝓤 ̇ } → is-hae (Id-to-Eq X Y)
Id-to-Eq-is-hae ua ua⁺ {X} {Y} = equivs-are-haes↓ ua⁺ (Id-to-Eq X Y) (ua X Y)

global-property-of-types : 𝓤ω
global-property-of-types = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇

cumulative : global-property-of-types → 𝓤ω
cumulative A = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X)

global-≃-ap : Univalence
            → (A : global-property-of-types)
            → cumulative A
            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y

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

global-≃-ap ua = global-≃-ap' ua id

subtypes-of : 𝓤 ̇ → 𝓤 ⁺ ̇
subtypes-of {𝓤} Y = Σ \(X : 𝓤 ̇ ) → X ↪ Y

_/[_]_ : (𝓤 : Universe) → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 /[ P ] Y = Σ \(X : 𝓤 ̇ ) → Σ \(f : X → Y) → (y : Y) → P (fiber f y)

χ-special : (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ ) → 𝓤 /[ P ] Y  → (Y → Σ P)
χ-special P Y (X , f , φ) y = fiber f y , φ y

is-special-map-classifier : (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-special-map-classifier {𝓤} P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)

mc-gives-sc : is-map-classifier 𝓤
            → (P : 𝓤 ̇ → 𝓥 ̇ ) → is-special-map-classifier P
mc-gives-sc {𝓤} s P Y = γ
 where
  h : is-hae (χ Y)
  h = invertibles-are-haes (χ Y) (equivs-are-invertible (χ Y) (s Y))

  e = (𝓤 /[ P ] Y)                               ≃⟨ ≃-sym a ⟩
      (Σ \(σ : 𝓤 / Y) → (y : Y) → P ((χ Y) σ y)) ≃⟨ ≃-sym b ⟩
      (Σ \(A : Y → 𝓤 ̇ ) → (y : Y) → P (A y))     ≃⟨ ≃-sym c ⟩
      (Y → Σ P)                                  ■
   where
    a = Σ-assoc
    b = Σ-change-of-variables-hae (λ A → Π (P ∘ A)) (χ Y) h
    c = ΠΣ-distr-≃

  observation : χ-special P Y ≡ Eq-to-fun e
  observation = refl _

  γ : is-equiv (χ-special P Y)
  γ = Eq-to-fun-is-equiv e

special-map-classifier : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                       → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                       → 𝓤 /[ P ] Y ≃ (Y → Σ P)
special-map-classifier {𝓤} ua fe P Y =
 χ-special P Y , mc-gives-sc (universes-are-map-classifiers ua fe) P Y

Ω-is-subtype-classifier : Univalence
                        → (Y : 𝓤 ̇ ) → subtypes-of Y ≃ (Y → Ω 𝓤)
Ω-is-subtype-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                  (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                  is-subsingleton

subtypes-form-set : Univalence → (Y : 𝓤 ̇ ) → is-set (subtypes-of Y)
subtypes-form-set {𝓤} ua Y = equiv-to-set
                              (Ω-is-subtype-classifier ua Y)
                              (powersets-are-sets
                                (univalence-gives-hfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                                (univalence-gives-dfunext (ua 𝓤))
                                (univalence-gives-propext (ua 𝓤)))

𝓢 : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓢 𝓤 = Σ \(S : 𝓤 ̇ ) → is-singleton S

equiv-classification : Univalence
                     → (Y : 𝓤 ̇ ) → (Σ \(X : 𝓤 ̇ ) → X ≃ Y) ≃ (Y → 𝓢 𝓤)
equiv-classification {𝓤} ua = special-map-classifier (ua 𝓤)
                               (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))
                               is-singleton

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
    p = pe (singletons-are-subsingletons (Lift 𝓤 𝟙) i)
           (singletons-are-subsingletons S s)
           (λ _ → center S s) (λ _ → center (Lift 𝓤 𝟙) i)

univalence-→-again : Univalence
                   → (Y : 𝓤 ̇ ) → is-singleton (Σ \(X : 𝓤 ̇ ) → X ≃ Y)
univalence-→-again {𝓤} ua Y = equiv-to-singleton (equiv-classification ua Y) i
 where
  i : is-singleton (Y → 𝓢 𝓤)
  i = univalence-gives-vvfunext' (ua 𝓤) (ua (𝓤 ⁺))
        (λ y → the-singletons-form-a-singleton
                (univalence-gives-propext (ua 𝓤))
                (univalence-gives-dfunext (ua 𝓤)))

module magma-equivalences (ua : Univalence) where

 dfe : global-dfunext
 dfe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

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

 is-magma-equiv : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-equiv M N f = is-equiv f × is-magma-hom M N f

 being-magma-equiv-is-a-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                     → is-subsingleton (is-magma-equiv M N f)
 being-magma-equiv-is-a-subsingleton M N f =
  ×-is-subsingleton
   (being-equiv-is-a-subsingleton dfe dfe f)
   (being-magma-hom-is-a-subsingleton M N f)

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
                                             ((ε b)⁻¹) ⟩
           g (f (g a) ·⟨ N ⟩ f (g b)) ≡⟨ ap g ((h (g a) (g b))⁻¹) ⟩
           g (f (g a ·⟨ M ⟩ g b))     ≡⟨ η (g a ·⟨ M ⟩ g b) ⟩
           g a ·⟨ M ⟩ g b             ∎

 magma-iso-charac : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                  → is-magma-iso M N f ≃ is-magma-equiv M N f
 magma-iso-charac M N f = logically-equivalent-subsingletons-are-equivalent
                           (is-magma-iso M N f)
                           (is-magma-equiv M N f)
                           (being-magma-iso-is-a-subsingleton M N f)
                           (being-magma-equiv-is-a-subsingleton M N f)
                           (magma-isos-are-magma-equivs M N f ,
                            magma-equivs-are-magma-isos M N f)

 magma-iso-charac' : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                   → is-magma-iso M N f ≡ is-magma-equiv M N f
 magma-iso-charac' M N f = Eq-to-Id (ua (universe-of ⟨ M ⟩))
                            (is-magma-iso M N f)
                            (is-magma-equiv M N f)
                            (magma-iso-charac M N f)

 magma-iso-charac'' : (M N : Magma 𝓤)
                    → is-magma-iso M N ≡ is-magma-equiv M N
 magma-iso-charac'' M N = dfe (magma-iso-charac' M N)

 _≃ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
 M ≃ₘ N = Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-equiv M N f

 ≅ₘ-charac : (M N : Magma 𝓤)
           → (M ≅ₘ N) ≃ (M ≃ₘ N)
 ≅ₘ-charac M N = Σ-cong (magma-iso-charac M N)

 ≅ₘ-charac' : (M N : Magma 𝓤)
            → (M ≅ₘ N) ≡ (M ≃ₘ N)
 ≅ₘ-charac' M N = ap Σ (magma-iso-charac'' M N)

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
               (pr₂-embedding (is-set X) (X → X → X)
                 (being-set-is-a-subsingleton dfe))
               (i , _·_)
               (j , _*_))
   b = happly _·_ _*_ , hfe _·_ _*_
   c = Π-cong dfe dfe X _ _ (λ x → happly (x ·_) (x *_) , hfe (x ·_) (x *_))

 magma-identity-is-equivalence : (M N : Magma 𝓤) → (M ≡ N) ≃ (M ≃ₘ N)
 magma-identity-is-equivalence {𝓤} M N =
  (M ≡ N)                                                                          ≃⟨ a ⟩
  (Σ \(p : ⟨ M ⟩ ≡ ⟨ N ⟩) → transport magma-structure p _·_ ≡ _*_)                 ≃⟨ b ⟩
  (Σ \(p : ⟨ M ⟩ ≡ ⟨ N ⟩) → is-magma-hom M N (Eq-to-fun (Id-to-Eq ⟨ M ⟩ ⟨ N ⟩ p))) ≃⟨ c ⟩
  (Σ \(e : ⟨ M ⟩ ≃ ⟨ N ⟩) → is-magma-hom M N (Eq-to-fun e))                        ≃⟨ Σ-assoc ⟩
  (Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-equiv f × is-magma-hom M N f)                       ■
  where
   _·_ = structure-of M
   _*_ = structure-of N
   a = Σ-≡-≃ M N
   b = Σ-cong (transport-of-magma-structure ⟨ M ⟩ ⟨ N ⟩ _·_ _*_)
   c = ≃-sym (Σ-change-of-variables-hae
                (λ e → is-magma-hom M N (Eq-to-fun e))
                (Id-to-Eq ⟨ M ⟩ ⟨ N ⟩)
                (Id-to-Eq-is-hae (ua 𝓤) (ua (𝓤 ⁺))))

 magma-identity-is-isomorphism : (M N : Magma 𝓤) → (M ≡ N) ≃ (M ≅ₘ N)
 magma-identity-is-isomorphism M N =
   (M ≡ N)  ≃⟨ magma-identity-is-equivalence M N ⟩
   (M ≃ₘ N) ≃⟨ ≃-sym (≅ₘ-charac M N) ⟩
   (M ≅ₘ N) ■

is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P

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

inhabited-induction : global-dfunext
                    → {X : 𝓤 ̇ } {P : is-inhabited X → 𝓤 ̇ }
                    → (i : (s : is-inhabited X) → is-subsingleton (P s))
                    → (f : (x : X) → P (pointed-is-inhabited x))
                    → (s : is-inhabited X) → P s
inhabited-induction fe {X} {P} i f s = φ' s
 where
  φ : X → P s
  φ x = transport P (inhabitation-is-a-subsingleton fe X (pointed-is-inhabited x) s)
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

image' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image' f = Σ \(y : codomain f) → is-inhabited (Σ \(x : domain f) → f x ≡ y)

restriction' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → image' f → Y
restriction' f (y , _) = y

corestriction' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → X → image' f
corestriction' f x = f x , pointed-is-inhabited (x , refl (f x))

is-surjection' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection' f = (y : codomain f) → is-inhabited (Σ \(x : domain f) → f x ≡ y)

record subsingleton-truncations-exist : 𝓤ω where
 field
  ∥_∥                  : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-a-subsingleton : {𝓤 : Universe} {X : 𝓤 ̇ } → is-subsingleton ∥ X ∥
  ∣_∣                 : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-recursion         : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                       → is-subsingleton P → (X → P) → ∥ X ∥ → P

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

  _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ∨ B = ∥ A + B ∥

  ∃ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃ A = ∥ Σ A ∥

  ∃! : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃! A = is-singleton (Σ A)

  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇ ) → ∥ X ∥ ⇔ is-inhabited X
  ∥∥-agrees-with-inhabitation X = a , b
   where
    a : ∥ X ∥ → is-inhabited X
    a = ∥∥-recursion (inhabitation-is-a-subsingleton fe X) pointed-is-inhabited
    b : is-inhabited X → ∥ X ∥
    b = inhabited-recursion X ∥ X ∥ ∥∥-is-a-subsingleton ∣_∣

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

  ∣∣-is-surjection : (X : 𝓤 ̇ ) → is-surjection (λ (x : X) → ∣ x ∣)
  ∣∣-is-surjection X s = γ
   where
    f : X → ∃ \(x : X) → ∣ x ∣ ≡ s
    f x = ∣ (x , ∥∥-is-a-subsingleton ∣ x ∣ s) ∣
    γ : ∃ \(x : X) → ∣ x ∣ ≡ s
    γ = ∥∥-recursion ∥∥-is-a-subsingleton f s

  AC : ∀ 𝓣 (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X → ((x : X) → is-set (A x)) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
  AC 𝓣 X A i j = (R : (x : X) → A x → 𝓣 ̇ )
               → ((x : X) (a : A x) → is-subsingleton (R x a))

               → ((x : X) → ∃ \(a : A x) → R x a)
               → ∃ \(f : (x : X) → A x) → (x : X) → R x (f x)

  Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
  Choice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ )
             (i : is-set X) (j : (x : X) → is-set (A x))
           → AC 𝓤 X A i j

  IAC : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
      → is-set X → ((x : X) → is-set (Y x)) → 𝓤 ⊔ 𝓥 ̇
  IAC X Y i j = ((x : X) → ∥ Y x ∥) → ∥ Π Y ∥

  IChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  IChoice 𝓤 = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
              (i : is-set X) (j : (x : X) → is-set (Y x))
            → IAC X Y i j

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

_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺ ⊔ 𝓤 ̇
X has-size 𝓥 = Σ \(Y : 𝓥 ̇ ) → X ≃ Y

propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇ ) → is-subsingleton P → P has-size 𝓥

resize-up : (X : 𝓤 ̇ ) → X has-size (𝓤 ⊔ 𝓥)
resize-up {𝓤} {𝓥} X = (Lift 𝓥 X , ≃-Lift X)

resize-up-subsingleton : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-subsingleton {𝓤} {𝓥} P i = resize-up {𝓤} {𝓥} P

resize : propositional-resizing 𝓤 𝓥
       → (P : 𝓤 ̇ ) (i : is-subsingleton P) → 𝓥 ̇
resize ρ P i = pr₁ (ρ P i)

resize-is-a-subsingleton : (ρ : propositional-resizing 𝓤 𝓥)
                           (P : 𝓤 ̇ ) (i : is-subsingleton P)
                         → is-subsingleton (resize ρ P i)
resize-is-a-subsingleton ρ P i = equiv-to-subsingleton (≃-sym (pr₂ (ρ P i))) i

to-resize : (ρ : propositional-resizing 𝓤 𝓥)
            (P : 𝓤 ̇ ) (i : is-subsingleton P)
          → P → resize ρ P i
to-resize ρ P i = Eq-to-fun (pr₂ (ρ P i))

from-resize : (ρ : propositional-resizing 𝓤 𝓥)
              (P : 𝓤 ̇ ) (i : is-subsingleton P)
            → resize ρ P i → P
from-resize ρ P i = Eq-to-fun (≃-sym(pr₂ (ρ P i)))

Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

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
        P (Q (em P i)) i (j (em P i))  (f (em P i) , g (em P i))

has-size-is-a-subsingleton : Univalence
                           → (X : 𝓤 ̇ ) (𝓥 :  Universe)
                           → is-subsingleton (X has-size 𝓥)
has-size-is-a-subsingleton {𝓤} ua X 𝓥 = univalence→' (ua 𝓥) (ua (𝓤 ⊔ 𝓥)) X

PR-is-a-subsingleton : Univalence → is-subsingleton (propositional-resizing 𝓤 𝓥)
PR-is-a-subsingleton {𝓤} {𝓥} ua =
 Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ P → Π-is-subsingleton (univalence-gives-global-dfunext ua)
          (λ i → has-size-is-a-subsingleton ua P 𝓥))

Impredicativity : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Impredicativity 𝓤 𝓥 = (Ω 𝓤) has-size 𝓥

impredicativity : (𝓤 : Universe) → 𝓤 ⁺ ̇
impredicativity 𝓤 = Impredicativity 𝓤 𝓤

PR-gives-Impredicativity⁺ : global-propext
                          → global-dfunext
                          → Propositional-resizing
                          → Impredicativity 𝓤 (𝓥 ⁺)
PR-gives-Impredicativity⁺ {𝓤} {𝓥} pe fe ρ = γ
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-a-subsingleton ρ Q j
  ψ : Ω 𝓤 → Ω 𝓥
  ψ (P , i) = resize ρ P i , resize-is-a-subsingleton ρ P i
  η : (p : Ω 𝓤) → φ (ψ p) ≡ p
  η (P , i) = Ω-ext fe pe a b
   where
    a : resize ρ (resize ρ P i) (resize-is-a-subsingleton ρ P i) → P
    a = from-resize ρ P i
      ∘ from-resize ρ (resize ρ P i) (resize-is-a-subsingleton ρ P i)
    b : P → resize ρ (resize ρ P i) (resize-is-a-subsingleton ρ P i)
    b = to-resize ρ (resize ρ P i) (resize-is-a-subsingleton ρ P i)
      ∘ to-resize ρ P i
  ε : (q : Ω 𝓥) → ψ (φ q) ≡ q
  ε (Q , j) = Ω-ext fe pe a b
   where
    a : resize ρ (resize ρ Q j) (resize-is-a-subsingleton ρ Q j) → Q
    a = from-resize ρ Q j
      ∘ from-resize ρ (resize ρ Q j) (resize-is-a-subsingleton ρ Q j)
    b : Q → resize ρ (resize ρ Q j) (resize-is-a-subsingleton ρ Q j)
    b = to-resize ρ (resize ρ Q j) (resize-is-a-subsingleton ρ Q j)
      ∘ to-resize ρ Q j
  γ : (Ω 𝓤) has-size (𝓥 ⁺)
  γ = Ω 𝓥 , invertibility-gives-≃ ψ (φ , η , ε)

PR-gives-impredicativity⁺ : global-propext
                          → global-dfunext
                          → Propositional-resizing
                          → impredicativity (𝓤 ⁺)
PR-gives-impredicativity⁺ = PR-gives-Impredicativity⁺

PR-gives-impredicativity₁ : global-propext
                          → global-dfunext
                          → Propositional-resizing
                          → Impredicativity 𝓤 𝓤₁
PR-gives-impredicativity₁ = PR-gives-Impredicativity⁺

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
  down = Eq-to-fun e
  O-is-set : is-set O
  O-is-set = equiv-to-set (≃-sym e) (Ω-is-a-set fe pe)
  Q : 𝓥 ̇
  Q = down (𝟙' , k) ≡ down (P , i)
  j : is-subsingleton Q
  j = O-is-set (down (Lift 𝓤 𝟙 , k)) (down (P , i))
  φ : Q → P
  φ q = Id-to-fun
         (ap _holds (equivs-are-lc down (Eq-to-fun-is-equiv e) q))
         (lift ⋆)
  γ : P → Q
  γ p = ap down (to-Σ-≡ (pe k i (λ _ → p) (λ _ → lift ⋆) ,
                         being-subsingleton-is-a-subsingleton fe _ _))
  ε : P ≃ Q
  ε = logically-equivalent-subsingletons-are-equivalent P Q i j (γ , φ)

PR-gives-existence-of-truncations : global-dfunext
                                  → Propositional-resizing
                                  → subsingleton-truncations-exist
PR-gives-existence-of-truncations fe R =
 record
 {
   ∥_∥ =

    λ {𝓤} X → resize R
               (is-inhabited X)
               (inhabitation-is-a-subsingleton fe X) ;

   ∥∥-is-a-subsingleton =

    λ {𝓤} {X} → resize-is-a-subsingleton R
                 (is-inhabited X)
                 (inhabitation-is-a-subsingleton fe X) ;

   ∣_∣ =

    λ {𝓤} {X} x → to-resize R
                   (is-inhabited X)
                   (inhabitation-is-a-subsingleton fe X)
                   (pointed-is-inhabited x) ;

   ∥∥-recursion =

    λ {𝓤} {𝓥} {X} {P} i u s → from-resize R P i
                                (inhabited-recursion X
                                  (resize R P i)
                                  (resize-is-a-subsingleton R P i)
                                  (to-resize R P i ∘ u)
                                  (from-resize R
                                    (is-inhabited X)
                                    (inhabitation-is-a-subsingleton fe X) s))
 }

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

  open ℕ-order
  open Arithmetic renaming (_+_ to _∔_)
  open BasicArithmetic

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
                                being-embedding-is-a-subsingleton fe f' _ e')
  γ : is-subsingleton X ≡ (X ↪ 𝟙)
  γ = pe (being-subsingleton-is-a-subsingleton fe) b (pr₁ a) (pr₂ a)

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
 retractions-into Y                                               ≃⟨ i ⟩
 (Σ \(X : 𝓤 ̇ ) → Σ \(f : X → Y) → (y : Y) → Σ \(x : X) → f x ≡ y) ≃⟨ ≃-refl _ ⟩
 ((𝓤 /[ id ] Y))                                                  ≃⟨ ii ⟩
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

  fe : global-dfunext
  fe = univalence-gives-global-dfunext ua

  open basic-truncation-development pt fe public

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

positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)

𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚

lifttwo : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ≡ 𝟚) ≡ Lift 𝓤₁ 𝟚

DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → ¬¬ P → P

neg-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ ) → is-subsingleton (¬ X)

emsanity : dfunext 𝓤 𝓤₀ → (P : 𝓤 ̇ )
         → is-subsingleton P → is-subsingleton (P + ¬ P)

ne : (X : 𝓤 ̇ ) → ¬¬(X + ¬ X)

DNE-gives-EM : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤

EM-gives-DNE : EM 𝓤 → DNE 𝓤

SN : ∀ 𝓤 → 𝓤 ⁺ ̇
SN 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → Σ \(X : 𝓤 ̇ ) → P ⇔ ¬ X

SN-gives-DNE : SN 𝓤 → DNE 𝓤

DNE-gives-SN : DNE 𝓤 → SN 𝓤

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
      q = succ (e n n)  ≡⟨ refl (α n) ⟩
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

lifttwo = sol
 where
  sol : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ≡ 𝟚) ≡ Lift 𝓤₁ 𝟚
  sol ua₀ ua₁ = Eq-to-Id ua₁ (𝟚 ≡ 𝟚) (Lift 𝓤₁ 𝟚) e
   where
    e = (𝟚 ≡ 𝟚)   ≃⟨ Id-to-Eq 𝟚 𝟚 , ua₀ 𝟚 𝟚 ⟩
        (𝟚 ≃ 𝟚)   ≃⟨ 𝟚-has-𝟚-automorphisms (univalence-gives-dfunext ua₀) ⟩
        𝟚         ≃⟨ ≃-sym (Lift-≃ 𝟚) ⟩
        Lift 𝓤₁ 𝟚 ■

neg-is-subsingleton = sol
 where
  sol : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ ) → is-subsingleton (¬ X)
  sol fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))

emsanity = sol
 where
  sol : dfunext 𝓤 𝓤₀ → (P : 𝓤 ̇ )
      → is-subsingleton P → is-subsingleton (P + ¬ P)
  sol fe P i (inl p) (inl q) = ap inl (i p q)
  sol fe P i (inl p) (inr n) = !𝟘 (inl p ≡ inr n) (n p)
  sol fe P i (inr m) (inl q) = !𝟘 (inr m ≡ inl q) (m q)
  sol fe P i (inr m) (inr n) = ap inr (neg-is-subsingleton fe P m n)

ne = sol
 where
  sol : (X : 𝓤 ̇ ) → ¬¬(X + ¬ X)
  sol X = λ (f : ¬(X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM = sol
 where
  sol : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤
  sol fe dne P i = dne (P + ¬ P) (emsanity fe P i) (ne P)

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
  sol dne P i = (¬ P) , dni P , dne P i

infix  4 _∼_
infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_
infix  0 _≡_
infixl 2 _∙_
infixr 0 _≡⟨_⟩_
infix  1 _∎
infix  3 _⁻¹
infix  0 _◁_
infix  1 _◀
infixr 0 _◁⟨_⟩_
infix  0 _≃_
infixl 2 _●_
infixr 0 _≃⟨_⟩_
infix  1 _■

