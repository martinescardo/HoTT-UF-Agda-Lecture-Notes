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

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
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

  infixl 20 _+_
  infixl 21 _×_

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
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
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
            → ((x : X) (y : Y x) → A (x , y))
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

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (Y → X)
rl-implication = pr₂

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

Id→Fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))

Id→Fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→Fun' (refl X) = 𝑖𝑑 X

Id→Funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
              → Id→Fun p ≡ Id→Fun' p

Id→Funs-agree (refl X) = refl (𝑖𝑑 X)

𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p ⋆

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

decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : (X : 𝓤 ̇ ) → 𝓤 ̇
has-decidable-equality X = (x y : X) → decidable (x ≡ y)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
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

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : decidable (x ≡ y) → decidable (succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))

module basic-arithmetic where

  open ℕ-order
  open Arithmetic renaming (_+_ to _∔_)

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

  +-assoc' : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc' x y zero     = refl _
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)

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

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ \(c : X) → (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ

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

is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop        = is-subsingleton
is-truth-value = is-subsingleton

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)

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

no-unicorns : ¬(Σ \(X : 𝓤 ̇ ) → is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , i , f , g) = c
 where
  e : is-empty X
  e x = f (pointed-subsingletons-are-singletons X x i)

  c : 𝟘
  c = g e

module magmas where

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

 magma-Id→iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
 magma-Id→iso p = (⌜ p ⌝ , ⌜⌝-is-iso p )

 ∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
 ∞-Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → X → X → X

module monoids where

 left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
 left-neutral e _·_ = ∀ x → e · x ≡ x

 right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
 right-neutral e _·_ = ∀ x → x · e ≡ x

 associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
 associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z)

 Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Monoid 𝓤 = Σ \(X : 𝓤 ̇ )
          → is-set X
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

to-Σ-≡' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {x : X} {a a' : A x}
        → a ≡ a' → Id (Σ A) (x , a) (x , a')

to-Σ-≡' {𝓤} {𝓥} {X} {A} {x} = ap (λ - → (x , -))

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)

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
 p                       ≡⟨ a y p                                     ⟩
 f x (refl x)⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 f x (refl x)⁻¹ ∙ f y q  ≡⟨ (a y q)⁻¹                                 ⟩
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

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingletons-are-sets 𝟘 𝟘-is-subsingleton

𝟙-is-set : is-set 𝟙
𝟙-is-set = subsingletons-are-sets 𝟙 𝟙-is-subsingleton

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
X has-minimal-hlevel 0        = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) × ¬(X is-of-hlevel n)

_has-minimal-hlevel-∞ : 𝓤 ̇ → 𝓤 ̇
X has-minimal-hlevel-∞ = (n : ℕ) → ¬(X is-of-hlevel n)

hedberg : {X : 𝓤 ̇ } → has-decidable-equality X → is-set X
hedberg {𝓤} {X} d = Id-collapsibles-are-sets X ic
 where
  ic : Id-collapsible X
  ic x y = f (d x y) , κ (d x y)
   where
    f : decidable (x ≡ y) → x ≡ y → x ≡ y
    f (inl p) q = p
    f (inr g) q = !𝟘 (x ≡ y) (g q)

    κ : (d : (x ≡ y) + ¬(x ≡ y)) → wconstant (f d)
    κ (inl p) q r = refl p
    κ (inr g) q r = !𝟘 (f (inr g) q ≡ f (inr g) r) (g q)

ℕ-is-set : is-set ℕ
ℕ-is-set = hedberg ℕ-has-decidable-equality

𝟚-is-set : is-set 𝟚
𝟚-is-set = hedberg 𝟚-has-decidable-equality

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

id-◁ : (X : 𝓤 ̇ ) → X ◁ X
id-◁ X = 𝑖𝑑 X , 𝑖𝑑 X , refl

_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
  η'' = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
              r (s x)           ≡⟨ η x             ⟩
              x                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = id-◁ X

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
            r (s y) ≡⟨ η y            ⟩
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
            g (f x)           ≡⟨ gf x             ⟩
            x                 ∎

  ε = λ z → f' (f (g (g' z))) ≡⟨ ap f' (fg (g' z)) ⟩
            f' (g' z)         ≡⟨ fg' z             ⟩
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

_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

Eq→fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq→fun (f , i) = f

Eq→fun-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (Eq→fun e)
Eq→fun-is-equiv (f , i) = i

invertibility-gives-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → invertible f → X ≃ Y

invertibility-gives-≃ f i = f , invertibles-are-equivs f i

Σ-induction-≃ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
              → ((x : X) (y : Y x) → A (x , y)) ≃ ((z : Σ Y) → A z)

Σ-induction-≃ = invertibility-gives-≃ Σ-induction (curry , refl , refl)

id-≃ : (X : 𝓤 ̇ ) → X ≃ X
id-≃ X = 𝑖𝑑 X , id-is-equiv X

_●_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
(f , d) ● (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverse-is-equiv f e

_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = id-≃

transport-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)

transport-is-equiv A (refl x) = id-is-equiv (A x)

Σ-≡-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ τ : Σ A)
      → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)

Σ-≡-≃ {𝓤} {𝓥} {X} {A}  σ τ = invertibility-gives-≃ from-Σ-≡ (to-Σ-≡ , η , ε)
 where
  η : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  η (refl σ) = refl (refl σ)

  ε : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
    → from-Σ-≡ (to-Σ-≡ w) ≡ w
  ε (refl p , refl q) = refl (refl p , refl q)

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

Id→Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id→Eq X X (refl X) = id-≃ X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id→Eq X Y)

univalence-≃ : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → (X ≡ Y) ≃ (X ≃ Y)
univalence-≃ ua X Y = Id→Eq X Y , ua X Y

Eq→Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq→Id ua X Y = inverse (Id→Eq X Y) (ua X Y)

Id→fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→fun {𝓤} {X} {Y} p = Eq→fun (Id→Eq X Y p)

Id→funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
              → Id→fun p ≡ Id→Fun p
Id→funs-agree (refl X) = refl (𝑖𝑑 X)

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
 e₀ = id-≃ 𝟚
 e₁ = swap₂ , swap₂-is-equiv

 e₀-is-not-e₁ : e₀ ≢ e₁
 e₀-is-not-e₁ p = ₁-is-not-₀ r
  where
   q : id ≡ swap₂
   q = ap Eq→fun p

   r : ₁ ≡ ₀
   r = ap (λ - → - ₁) q

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

 𝓤₀-is-not-a-set : ¬(is-set (𝓤₀ ̇ ))
 𝓤₀-is-not-a-set s = p₀-is-not-p₁ q
  where
   q : p₀ ≡ p₁
   q = s 𝟚 𝟚 p₀ p₁

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

univalence⇒ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-singleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)

univalence⇒ ua X = equiv-singleton-lemma X (Id→Eq X) (ua X)

⇒univalence : ((X : 𝓤 ̇ ) → is-singleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y))
            → is-univalent 𝓤

⇒univalence i X = singleton-equiv-lemma X (Id→Eq X) (i X)

univalence→ : is-univalent 𝓤
            → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y)

univalence→ ua X = singletons-are-subsingletons
                    (Σ (X ≃_)) (univalence⇒ ua X)

→univalence : ((X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ̇ ) → X ≃ Y))
            → is-univalent 𝓤

→univalence i = ⇒univalence (λ X → pointed-subsingletons-are-singletons
                                    (Σ (X ≃_)) (X , id-≃ X) (i X))

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

J-≃ : is-univalent 𝓤
    → (A : (X Y : 𝓤 ̇ ) → X ≃ Y → 𝓥 ̇ )
    → ((X : 𝓤 ̇ ) → A X X (id-≃ X))
    → (X Y : 𝓤 ̇ ) (e : X ≃ Y) → A X Y e

J-≃ ua A φ X = H-≃ ua X (A X) (φ X)

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

Σ-change-of-variable'' : is-univalent 𝓤
                       → {X : 𝓤 ̇ } {Y : 𝓤 ̇ } (A : Y → 𝓥 ̇ ) (f : X → Y)
                       → is-equiv f
                       → (Σ \(y : Y) → A y) ≡ (Σ \(x : X) → A (f x))

Σ-change-of-variable'' ua A f i = Σ-change-of-variable' ua A
                                  (inverse f i)
                                  (inverse-is-equiv f i)

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

ua-equivs-are-haes : is-univalent 𝓤
                   → {X Y : 𝓤 ̇ } (f : X → Y)
                   → is-equiv f → is-hae f

ua-equivs-are-haes ua {X} {Y} = J-equiv ua (λ X Y f → is-hae f) id-is-hae X Y

ua-invertibles-are-haes : is-univalent 𝓤
                        → {X Y : 𝓤 ̇ } (f : X → Y)
                        → invertible f → is-hae f

ua-invertibles-are-haes ua f i = ua-equivs-are-haes ua f (invertibles-are-equivs f i)

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

funext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g

precomp-is-equiv : is-univalent 𝓤
                 → (X Y : 𝓤 ̇ ) (f : X → Y)
                 → is-equiv f
                 → (Z : 𝓤 ̇ ) → is-equiv (λ (g : Y → Z) → g ∘ f)

precomp-is-equiv {𝓤} ua =
   J-equiv ua
     (λ X Y (f : X → Y) → (Z : 𝓤 ̇ ) → is-equiv (λ g → g ∘ f))
     (λ X Z → id-is-equiv (X → Z))

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

  γ' : f₀ ∼ f₁ → f₀ ≡ f₁
  γ' h = f₀                             ≡⟨ refl _                               ⟩
         (λ x → f₀ x)                   ≡⟨ refl _                               ⟩
         (λ x → π₀ (f₀ x , f₁ x , h x)) ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) q ⟩
         (λ x → π₁ (f₀ x , f₁ x , h x)) ≡⟨ refl _                               ⟩
         (λ x → f₁ x)                   ≡⟨ refl _                               ⟩
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

map-classification : is-univalent 𝓤 → dfunext 𝓤 (𝓤 ⁺)
                   → (Y : 𝓤 ̇ ) → 𝓤 / Y ≃ (Y → 𝓤 ̇ )

map-classification ua fe Y = χ Y , universes-are-map-classifiers ua fe Y

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

Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-subsingletonω : Univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-subsingletonω {𝓤} γ = univalence-is-subsingleton (γ (𝓤 ⁺))

univalence-is-a-singleton : Univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-singleton {𝓤} γ = pointed-subsingletons-are-singletons
                                   (is-univalent 𝓤)
                                   (γ 𝓤)
                                   (univalence-is-subsingletonω γ)

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

Π-is-subsingleton' : dfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                   → ((x : X) → is-subsingleton (A x))
                   → is-subsingleton ({x : X} → A x)

Π-is-subsingleton' fe {X} {A} i = γ
 where
  ρ : ({x : X} → A x) ◁ Π A
  ρ = (λ f {x} → f x) , (λ g x → g {x}) , refl

  γ : is-subsingleton ({x : X} → A x)
  γ = retract-of-subsingleton ρ (Π-is-subsingleton fe i)

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

weak-unique-existence-gives-unique-existence-sometimes : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) →

    ((x : X) → is-subsingleton (A x))

  → ((Σ \(x : X) → A x) × ((x y : X) → A x → A y → x ≡ y))
  → (∃! \(x : X) → A x)

weak-unique-existence-gives-unique-existence-sometimes A i ((x , a) , u) = (x , a) , φ
 where
  φ : (σ : Σ A) → x , a ≡ σ
  φ (y , b) = to-Σ-≡ (u x y a b , i y _ _)

ℕ-is-nno : hfunext 𝓤₀ 𝓤
         → (Y : 𝓤 ̇ ) (y₀ : Y) (g : Y → Y)
         → ∃! \(h : ℕ → Y) → (h 0 ≡ y₀) × (h ∘ succ ≡ g ∘ h)

ℕ-is-nno {𝓤} hfe Y y₀ g = γ
 where

  fe : dfunext 𝓤₀ 𝓤
  fe = hfunext-gives-dfunext hfe

  lemma₀ : (h : ℕ → Y) → ((h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h)) ◁ (h ∼ ℕ-iteration Y y₀ g)
  lemma₀ h = r , s , η
   where
    s : (h 0 ≡ y₀) × (h ∘ succ ∼ g ∘ h) → h ∼ ℕ-iteration Y y₀ g
    s (p , K) 0 = p
    s (p , K) (succ n) = h (succ n)                  ≡⟨ K n                ⟩
                         g (h n)                     ≡⟨ ap g (s (p , K) n) ⟩
                         g (ℕ-iteration Y y₀ g n)    ≡⟨ refl _             ⟩
                         ℕ-iteration Y y₀ g (succ n) ∎

    r : codomain s → domain s
    r H = H 0 , (λ n → h (succ n)                  ≡⟨ H (succ n)     ⟩
                       ℕ-iteration Y y₀ g (succ n) ≡⟨ refl _         ⟩
                       g (ℕ-iteration Y y₀ g n)    ≡⟨ ap g ((H n)⁻¹) ⟩
                       g (h n )                    ∎)

    remark : ∀ n H → pr₂ (r H) n ≡ H (succ n) ∙ (refl _ ∙ ap g ((H n)⁻¹))
    remark n H = refl _

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

hlevel-relation-is-subsingleton : dfunext 𝓤 𝓤
                                → (n : ℕ) (X : 𝓤 ̇ )
                                → is-subsingleton (X is-of-hlevel n)

hlevel-relation-is-subsingleton {𝓤} fe zero X =
 being-singleton-is-subsingleton fe

hlevel-relation-is-subsingleton fe (succ n) X =
 Π-is-subsingleton fe
  (λ x → Π-is-subsingleton fe
  (λ x' → hlevel-relation-is-subsingleton fe n (x ≡ x')))

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

emptiness-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ )
                          → is-subsingleton (is-empty X)
emptiness-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))

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

propext : ∀ 𝓤  → 𝓤 ⁺ ̇
propext 𝓤 = {P Q : 𝓤 ̇ } → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

global-propext : 𝓤ω
global-propext = ∀ {𝓤} → propext 𝓤

univalence-gives-propext : is-univalent 𝓤 → propext 𝓤
univalence-gives-propext ua {P} {Q} i j f g =
 Eq→Id ua P Q
  (logically-equivalent-subsingletons-are-equivalent P Q i j (f , g))

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

Ω-is-a-set : dfunext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-a-set {𝓤} fe pe = Id-collapsibles-are-sets (Ω 𝓤) c
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

powersets-are-sets : hfunext 𝓤 (𝓥 ⁺) → dfunext 𝓥 𝓥 → propext 𝓥
                   → {X : 𝓤 ̇ } → is-set (X → Ω 𝓥)
powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-a-set fe' pe)

𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

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

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } (A B : 𝓟 X)
                       → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-dfunext (ua 𝓤))
                                 (univalence-gives-dfunext' (ua 𝓤) (ua (𝓤 ⁺)))

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

Eq-Eq-cong : global-dfunext
           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
           → X ≃ A → Y ≃ B → (X ≃ Y) ≃ (A ≃ B)

Eq-Eq-cong fe = Eq-Eq-cong' fe fe fe fe fe fe fe fe fe fe fe fe

is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = (y : codomain f) → is-subsingleton (fiber f y)

being-embedding-is-subsingleton : global-dfunext
                                → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → is-subsingleton (is-embedding f)

being-embedding-is-subsingleton fe f =
 Π-is-subsingleton fe
  (λ x → being-subsingleton-is-subsingleton fe)

pr₂-embedding : (A : 𝓤 ̇ ) (X : 𝓥 ̇ )
              → is-subsingleton A
              → is-embedding (λ (z : A × X) → pr₂ z)

pr₂-embedding A X i x ((a , x) , refl x) ((b , x) , refl x) = p
 where
  p : ((a , x) , refl x) ≡ ((b , x) , refl x)
  p = ap (λ - → ((- , x) , refl x)) (i a b)

pr₁-embedding : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
              → ((x : X) → is-subsingleton (A x))
              → is-embedding (pr₁ {𝓤} {𝓥} {X} {A})
pr₁-embedding i x ((x , a) , refl x) ((x , a') , refl x) = γ
 where
  γ : (x , a) , refl x ≡ (x , a') , refl x
  γ = ap (λ - → (x , -) , refl x) (i x a a')

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
  γ x = singleton-equiv-lemma x (λ x' → ap f {x} {x'})
         (pointed-subsingletons-are-singletons
           (Σ \(x' : X) → f x ≡ f x') (x , (refl (f x))) (s x))

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

𝓔 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X) → Nat (𝓨 x) A → A x
𝓔 A x τ = τ x (refl x)

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

Yoneda-Lemma : dfunext 𝓤 (𝓤 ⊔ 𝓥) → dfunext 𝓤 𝓥
             → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (x : X)
             → Nat (𝓨 x) A ≃ A x

Yoneda-Lemma fe fe' A x = 𝓔 A x , 𝓔-is-equiv fe fe' A x

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

record Lift {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 constructor
  lift
 field
  lower : X

open Lift public

type-of-Lift  :             type-of (Lift  {𝓤} 𝓥)       ≡ (𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
type-of-lift  : {X : 𝓤 ̇ } → type-of (lift  {𝓤} {𝓥} {X}) ≡ (X → Lift 𝓥 X)
type-of-lower : {X : 𝓤 ̇ } → type-of (lower {𝓤} {𝓥} {X}) ≡ (Lift 𝓥 X → X)

type-of-Lift  = refl _
type-of-lift  = refl _
type-of-lower = refl _

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

univalence→'' : is-univalent (𝓤 ⊔ 𝓥)
              → (X : 𝓤 ̇ ) → is-subsingleton (Σ \(Y : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)

univalence→'' ua = univalence→' ua ua

univalence→''-dual : is-univalent (𝓤 ⊔ 𝓥)
                   → (Y : 𝓤 ̇ ) → is-subsingleton (Σ \(X : 𝓤 ⊔ 𝓥 ̇ ) → X ≃ Y)

univalence→''-dual ua = univalence→'-dual ua ua

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

Id→Eq-is-hae' : is-univalent 𝓤 → is-univalent (𝓤 ⁺)
              → {X Y : 𝓤 ̇ } → is-hae (Id→Eq X Y)

Id→Eq-is-hae' ua ua⁺ {X} {Y} = equivs-are-haes↓ ua⁺ (Id→Eq X Y) (ua X Y)

Id→Eq-is-hae : is-univalent 𝓤
             → {X Y : 𝓤 ̇ } → is-hae (Id→Eq X Y)

Id→Eq-is-hae ua {X} {Y} = invertibles-are-haes (Id→Eq X Y)
                           (equivs-are-invertible (Id→Eq X Y) (ua X Y))

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
  φ (S , s) = to-Σ-≡ (p , being-singleton-is-subsingleton fe _ _)
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

 open magmas

 dfe : global-dfunext
 dfe = univalence-gives-global-dfunext ua

 hfe : global-hfunext
 hfe = univalence-gives-global-hfunext ua

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

 is-magma-equiv : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-equiv M N f = is-equiv f × is-magma-hom M N f

 being-magma-equiv-is-subsingleton : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                                   → is-subsingleton (is-magma-equiv M N f)

 being-magma-equiv-is-subsingleton M N f =
  ×-is-subsingleton
   (being-equiv-is-subsingleton dfe dfe f)
   (being-magma-hom-is-subsingleton M N f)

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

 magma-iso-charac : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                  → is-magma-iso M N f ≃ is-magma-equiv M N f

 magma-iso-charac M N f = logically-equivalent-subsingletons-are-equivalent
                           (is-magma-iso M N f)
                           (is-magma-equiv M N f)
                           (being-magma-iso-is-subsingleton M N f)
                           (being-magma-equiv-is-subsingleton M N f)
                           (magma-isos-are-magma-equivs M N f ,
                            magma-equivs-are-magma-isos M N f)

 magma-iso-charac' : (M N : Magma 𝓤) (f : ⟨ M ⟩ → ⟨ N ⟩)
                   → is-magma-iso M N f ≡ is-magma-equiv M N f

 magma-iso-charac' M N f = Eq→Id (ua (universe-of ⟨ M ⟩))
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

module sip where

 ⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
 ⟨ X , s ⟩ = X

 structure : {S : 𝓤 ̇ → 𝓥 ̇ } (A : Σ S) → S ⟨ A ⟩
 structure (X , s) = s

 canonical-map : {S : 𝓤 ̇ → 𝓥 ̇ }
                 (ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                 (ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
                 {X : 𝓤 ̇ }
                 (s t : S X)

               → s ≡ t → ι (X , s) (X , t) (id-≃ X)

 canonical-map ι ρ {X} s s (refl s) = ρ (X , s)

 SNS : (𝓤 ̇ → 𝓥 ̇ ) → (𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇

 SNS {𝓤} {𝓥} S 𝓦 = Σ \(ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇ )
                 → Σ \(ρ : (A : Σ S) → ι A A (id-≃ ⟨ A ⟩))
                 → {X : 𝓤 ̇ } (s t : S X) → is-equiv (canonical-map ι ρ s t)

 homomorphic : {S : 𝓤 ̇ → 𝓥 ̇ } → SNS S 𝓦
             → (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇

 homomorphic (ι , ρ , θ) = ι

 _≃[_]_ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → SNS S 𝓦 → Σ S → 𝓤 ⊔ 𝓦 ̇

 A ≃[ σ ] B = Σ \(f : ⟨ A ⟩ → ⟨ B ⟩)
            → Σ \(i : is-equiv f) → homomorphic σ A B (f , i)

 Id→homEq : {S : 𝓤 ̇ → 𝓥 ̇ } (σ : SNS S 𝓦)
          → (A B : Σ S) → (A ≡ B) → (A ≃[ σ ] B)

 Id→homEq (_ , ρ , _) A A (refl A) = id , id-is-equiv ⟨ A ⟩ , ρ A

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

 characterization-of-characterization-of-∞-Magma-≡ :

    (ua : is-univalent 𝓤) (A : ∞-Magma)
  →
    Eq→fun (characterization-of-∞-Magma-≡ ua A A) (refl A)
  ≡
    (𝑖𝑑 ⟨ A ⟩ , id-is-equiv ⟨ A ⟩ , refl _)

 characterization-of-characterization-of-∞-Magma-≡ ua A = refl _

module sip-with-axioms where

 open sip

 [_] : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → axioms X s) → Σ S

 [ X , s , _ ] = (X , s)

 ⟪_⟫ : {S : 𝓤 ̇ → 𝓥 ̇ } {axioms : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ }
     → (Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → axioms X s) → 𝓤 ̇

 ⟪ X , _ , _ ⟫ = X

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

module sip-join where

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

 _≃⟦_,_⟧_ : {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }

          → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X)
          → SNS S₀ 𝓦₀
          → SNS S₁ 𝓦₁
          → (Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X)

          → 𝓤 ⊔ 𝓦₀ ⊔ 𝓦₁ ̇

 A ≃⟦ σ₀ , σ₁ ⟧ B = Σ \(f : ⟪ A ⟫ → ⟪ B ⟫)
                  → Σ \(i : is-equiv f) → homomorphic σ₀ [ A ]₀ [ B ]₀ (f , i)
                                        × homomorphic σ₁ [ A ]₁ [ B ]₁ (f , i)

 characterization-of-join-≡ : is-univalent 𝓤
                            → {S₀ : 𝓤 ̇ → 𝓥 ̇ } {S₁ : 𝓤 ̇ → 𝓥₁ ̇ }
                              (σ₀ : SNS S₀ 𝓦₀)  (σ₁ : SNS S₁ 𝓦₁)

                              (A B : Σ \(X : 𝓤 ̇ ) → S₀ X × S₁ X)
                            →
                              (A ≡ B) ≃ (A ≃⟦ σ₀ , σ₁ ⟧ B)

 characterization-of-join-≡ ua σ₀ σ₁ = characterization-of-≡ ua (join σ₀ σ₁)

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

 _≅'_ : Group → Group → 𝓤 ̇

 (X , ((_·_ , d) , _) , _) ≅' (Y , ((_*_ , e) , _) , _) =

            Σ \(f : X → Y) → is-equiv f
                           × ((λ x x' → f (x · x')) ≡ (λ x x' → f x * f x'))

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

module generalized-topological-space-identity
        (𝓤 𝓥 : Universe)
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → ((X → R) → R) → 𝓤 ⊔ 𝓥 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (𝓞 : (X → R) → R) → is-subsingleton (axioms X 𝓞))
       where

 open sip
 open sip-with-axioms

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

 sns-data : SNS ℙℙ (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ ℙℙ) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , 𝓞X) (Y , 𝓞Y) (f , _) = (λ (V : ℙ Y) → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y

   ρ : (A : Σ ℙℙ) → ι A A (id-≃ ⟨ A ⟩)
   ρ (X , 𝓞) = refl 𝓞

   h : {X : 𝓤 ̇ } {𝓞 𝓞' : ℙℙ X} → canonical-map ι ρ 𝓞 𝓞' ∼ 𝑖𝑑 (𝓞 ≡ 𝓞')
   h (refl 𝓞) = refl (refl 𝓞)

   θ : {X : 𝓤 ̇ } (𝓞 𝓞' : ℙℙ X) → is-equiv (canonical-map ι ρ 𝓞 𝓞')
   θ {X} 𝓞 𝓞' = equivs-closed-under-∼ (id-is-equiv (𝓞 ≡ 𝓞')) h

 _≅_  : Space → Space → 𝓤 ⊔ 𝓥 ̇

 (X , 𝓞X , _) ≅ (Y , 𝓞Y , _) =

              Σ \(f : X → Y) → is-equiv f
                             × ((λ V → inverse-image f V ∊ 𝓞X) ≡ 𝓞Y)

 characterization-of-Space-≡ : is-univalent 𝓤
                             → (A B : Space)

                             → (A ≡ B) ≃ (A ≅ B)

 characterization-of-Space-≡ ua = characterization-of-≡-with-axioms ua
                                   sns-data axioms axiomss

 _≅'_  : Space → Space → 𝓤 ⊔ 𝓥 ̇

 (X , F , _) ≅' (Y , G , _) =

             Σ \(f : X → Y) → is-equiv f
                            × ((λ (v : Y → R) → F (v ∘ f)) ≡ G)

 characterization-of-Space-≡' : is-univalent 𝓤
                              → (A B : Space)

                              → (A ≡ B) ≃ (A ≅' B)

 characterization-of-Space-≡' = characterization-of-Space-≡

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

module generalized-functor-algebra-equality
         {𝓤 : Universe}
         (F : 𝓤 ̇ → 𝓤 ̇ )
         (𝓕 : {X Y : 𝓤 ̇ } → (X → Y) → F X → F Y)
         (𝓕-id : {X : 𝓤 ̇ } → 𝓕 (𝑖𝑑 X) ≡ 𝑖𝑑 (F X))
       where

 open sip

 S : 𝓤 ̇ → 𝓤 ̇
 S X = F X → X

 sns-data : SNS S 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
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

type-valued-preorder-S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
type-valued-preorder-S {𝓤} {𝓥} X = Σ \(_≤_ : X → X → 𝓥 ̇ )
                                 → ((x : X) → x ≤ x)
                                 × ((x y z : X) → x ≤ y → y ≤ z → x ≤ z)

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

 Ob : Σ S → 𝓤 ̇
 Ob (X , homX , idX , compX ) = X

 hom : (𝓧 : Σ S) → Ob 𝓧 → Ob 𝓧 → 𝓥 ̇
 hom (X , homX , idX , compX) = homX

 𝒾𝒹 : (𝓧 : Σ S) (x : Ob 𝓧) → hom 𝓧 x x
 𝒾𝒹 (X , homX , idX , compX) = idX

 comp : (𝓧 : Σ S) (x y z : Ob 𝓧) → hom 𝓧 x y → hom 𝓧 y z → hom 𝓧 x z
 comp (X , homX , idX , compX) = compX

 functorial : (𝓧 𝓐 : Σ S)
            → (F : Ob 𝓧 → Ob 𝓐)
            → ((x y : Ob 𝓧) → hom 𝓧 x y → hom 𝓐 (F x) (F y))
            → 𝓤 ⊔ 𝓥 ̇

 functorial 𝓧 𝓐 F 𝓕' = pidentity × pcomposition
  where

   _o_ : {x y z : Ob 𝓧} → hom 𝓧 y z → hom 𝓧 x y → hom 𝓧 x z
   g o f = comp 𝓧 _ _ _ f g

   _□_ : {a b c : Ob 𝓐} → hom 𝓐 b c → hom 𝓐 a b → hom 𝓐 a c
   g □ f = comp 𝓐 _ _ _ f g

   𝓕 : {x y : Ob 𝓧} → hom 𝓧 x y → hom 𝓐 (F x) (F y)
   𝓕 f = 𝓕' _ _ f

   pidentity = (λ x → 𝓕 (𝒾𝒹 𝓧 x)) ≡ (λ x → 𝒾𝒹 𝓐 (F x))

   pcomposition = (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 (g o f))
                ≡ (λ x y z (f : hom 𝓧 x y) (g : hom 𝓧 y z) → 𝓕 g □ 𝓕 f)

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

module category-identity
        (𝓤 𝓥 : Universe)
        (ua : Univalence)
      where

 open type-valued-preorder-with-axioms-identity 𝓤 𝓥 (𝓤 ⊔ 𝓥) ua

 fe : global-dfunext
 fe = univalence-gives-global-dfunext ua

 S : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
 S = type-valued-preorder-S {𝓤} {𝓥}

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

 Cat : (𝓤 ⊔ 𝓥)⁺ ̇
 Cat = Σ \(X : 𝓤 ̇ ) → Σ \(s : S X) → category-axioms X s

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

is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P

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

inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ )
                                          → is-subsingleton P → is-inhabited P → P

inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s (𝑖𝑑 P)

inhabited-functorial : global-dfunext → (X : 𝓤 ⁺ ̇ ) (Y : 𝓤 ̇ )
                     → (X → Y) → is-inhabited X → is-inhabited Y

inhabited-functorial fe X Y f = inhabited-recursion
                                  X
                                  (is-inhabited Y)
                                  (inhabitation-is-subsingleton fe Y)
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
  ∥∥-is-subsingleton   : {𝓤 : Universe} {X : 𝓤 ̇ } → is-subsingleton ∥ X ∥
  ∣_∣                  : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-recursion         : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ }
                       → is-subsingleton P → (X → P) → ∥ X ∥ → P

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

  ∥∥-agrees-with-inhabitation : (X : 𝓤 ̇ ) → ∥ X ∥ ⇔ is-inhabited X
  ∥∥-agrees-with-inhabitation X = a , b
   where
    a : ∥ X ∥ → is-inhabited X
    a = ∥∥-recursion (inhabitation-is-subsingleton hunapply X) pointed-is-inhabited

    b : is-inhabited X → ∥ X ∥
    b = inhabited-recursion X ∥ X ∥ ∥∥-is-subsingleton ∣_∣

  _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ∨ B = ∥ A + B ∥

  infixl 20 _∨_

  ∃ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  ∃ A = ∥ Σ A ∥

  ∨-is-subsingleton : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → is-subsingleton (A ∨ B)
  ∨-is-subsingleton = ∥∥-is-subsingleton

  ∃-is-subsingleton : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → is-subsingleton (∃ A)
  ∃-is-subsingleton = ∥∥-is-subsingleton

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

  ∣∣-is-surjection : (X : 𝓤 ̇ ) → is-surjection (λ (x : X) → ∣ x ∣)
  ∣∣-is-surjection X s = γ
   where
    f : X → ∃ \(x : X) → ∣ x ∣ ≡ s
    f x = ∣ (x , ∥∥-is-subsingleton ∣ x ∣ s) ∣

    γ : ∃ \(x : X) → ∣ x ∣ ≡ s
    γ = ∥∥-recursion ∥∥-is-subsingleton f s

  singletons-are-inhabited : (X : 𝓤 ̇ )
                           → is-singleton X
                           → ∥ X ∥

  singletons-are-inhabited X s = ∣ center X s ∣

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

  singleton-iff-inhabited-subsingleton : (X : 𝓤 ̇ )
                                       → is-singleton X
                                       ⇔ (∥ X ∥ × is-subsingleton X)

  singleton-iff-inhabited-subsingleton X =
    (λ (s : is-singleton X) → singletons-are-inhabited     X s ,
                              singletons-are-subsingletons X s) ,
    Σ-induction (inhabited-subsingletons-are-singletons X)

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

simple-unique-choice : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

                     → ((x : X) → ∃! \(a : A x) → R x a)
                     → Σ \(f : Π A) → (x : X) → R x (f x)

simple-unique-choice X A R s = f , φ
 where
  f : (x : X) → A x
  f x = pr₁ (center (Σ \(a : A x) → R x a) (s x))

  φ : (x : X) → R x (f x)
  φ x = pr₂ (center (Σ \(a : A x) → R x a) (s x))

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

unique-choice⇔vvfunext : Unique-Choice 𝓤 𝓥 𝓥 ⇔ vvfunext 𝓤 𝓥
unique-choice⇔vvfunext = unique-choice-gives-vvfunext ,
                         vvfunext-gives-unique-choice

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

module choice
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

  open basic-truncation-development pt hfe

  simple-unique-choice' : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (R : (x : X) → A x → 𝓦 ̇ )

                        → ((x : X) → is-subsingleton (Σ \(a : A x) → R x a))

                        → ((x : X) → ∃ \(a : A x) → R x a)
                        → Σ \(f : Π A) → (x : X) → R x (f x)

  simple-unique-choice' X A R u φ = simple-unique-choice X A R s
   where
    s : (x : X) → ∃! \(a : A x) → R x a
    s x = inhabited-subsingletons-are-singletons (Σ \(a : A x) → R x a) (φ x) (u x)

  AC : ∀ 𝓣 (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
     → is-set X → ((x : X) → is-set (A x)) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇

  AC 𝓣 X A i j = (R : (x : X) → A x → 𝓣 ̇ )
               → ((x : X) (a : A x) → is-subsingleton (R x a))

               → ((x : X) → ∃ \(a : A x) → R x a)
               → ∃ \(f : Π A) → (x : X) → R x (f x)

  Choice : ∀ 𝓤 → 𝓤 ⁺ ̇
  Choice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (A x))
           → AC 𝓤 X A i j

  IAC : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-set (Y x)) → 𝓤 ⊔ 𝓥 ̇
  IAC X Y i j = ((x : X) → ∥ Y x ∥) → ∥ Π Y ∥

  IChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  IChoice 𝓤 = (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (Y x))
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

  TAC : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → is-set X → ((x : X) → is-set (A x)) → 𝓤 ⊔ 𝓥 ̇
  TAC X A i j = ∥((x : X) → ∥ A x ∥ → A x)∥

  TChoice : ∀ 𝓤 → 𝓤 ⁺ ̇
  TChoice 𝓤 = (X : 𝓤 ̇ ) (A : X → 𝓤 ̇ ) (i : is-set X) (j : (x : X) → is-set (A x))
            → TAC X A i j

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

  global-choice : (𝓤 : Universe) → 𝓤 ⁺ ̇
  global-choice 𝓤 = (X : 𝓤 ̇ ) → X + is-empty X

  global-choice' : (𝓤 : Universe) → 𝓤 ⁺ ̇
  global-choice' 𝓤 = (X : 𝓤 ̇ ) → ∥ X ∥ → X

  global-choice-inconsistent-with-univalence : global-choice 𝓤₁
                                             → is-univalent 𝓤₀
                                             → 𝟘

  global-choice-inconsistent-with-univalence g ua = c
   where
    b : (X : 𝓤₁ ̇ ) → is-set X
    b X = hedberg (λ x y → g (x ≡ y))

    open example-of-a-nonset ua

    c : 𝟘
    c = 𝓤₀-is-not-a-set (b (𝓤₀ ̇ ))

  global-choice'-inconsistent-with-univalence : global-choice' 𝓤₁
                                              → is-univalent 𝓤₀
                                              → 𝟘

  global-choice'-inconsistent-with-univalence g ua = c
   where
    a : (X : 𝓤₁ ̇ ) → has-decidable-equality X
    a X x₀ x₁ = decidable-equality-criterion α (λ x → g (Σ \(n : 𝟚) → α n ≡ x))
     where
      α : 𝟚 → X
      α ₀ = x₀
      α ₁ = x₁

    b : (X : 𝓤₁ ̇ ) → is-set X
    b X = hedberg (a X)

    open example-of-a-nonset ua

    c : 𝟘
    c = 𝓤₀-is-not-a-set (b (𝓤₀ ̇ ))

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

has-size-is-subsingleton : Univalence
                         → (X : 𝓤 ̇ ) (𝓥 :  Universe)
                         → is-subsingleton (X has-size 𝓥)

has-size-is-subsingleton {𝓤} ua X 𝓥 = univalence→' (ua 𝓥) (ua (𝓤 ⊔ 𝓥)) X

PR-is-subsingleton : Univalence → is-subsingleton (propositional-resizing 𝓤 𝓥)
PR-is-subsingleton {𝓤} {𝓥} ua =
 Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ P → Π-is-subsingleton (univalence-gives-global-dfunext ua)
  (λ i → has-size-is-subsingleton ua P 𝓥))

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

PR-gives-impredicativity⁺ : global-propext
                          → global-dfunext
                          → propositional-resizing (𝓤 ⁺) 𝓤
                          → is-impredicative (𝓤 ⁺)

PR-gives-impredicativity⁺ pe fe = PR-gives-Impredicativity⁺
                                   pe fe (λ P i → resize-up P)

PR-gives-impredicativity₁ : global-propext
                          → global-dfunext
                          → propositional-resizing 𝓤 𝓤₀
                          → Impredicativity 𝓤 𝓤₁

PR-gives-impredicativity₁ pe fe = PR-gives-Impredicativity⁺
                                   pe fe (λ P i → resize-up P)

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

module powerset-union-existence
        (pt  : subsingleton-truncations-exist)
        (hfe : global-hfunext)
       where

 open basic-truncation-development pt hfe

 family-union : {X : 𝓤 ⊔ 𝓥 ̇ } {I : 𝓥 ̇ } → (I → 𝓟 X) → 𝓟 X
 family-union {𝓤} {𝓥} {X} {I} A = λ x → (∃ \(i : I) → x ∈ A i) , ∃-is-subsingleton

 𝓟𝓟 : 𝓤 ̇ → 𝓤 ⁺⁺ ̇
 𝓟𝓟 X = 𝓟 (𝓟 X)

 existence-of-unions : (𝓤 : Universe) → 𝓤 ⁺⁺ ̇
 existence-of-unions 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : 𝓟𝓟 X)
     → Σ \(B : 𝓟 X)
             → (x : X) → (x ∈ B) ⇔ ∃ \(A : 𝓟 X) → (A ∈ 𝓐) × (x ∈ A)

 existence-of-unions₁ : (𝓤 :  Universe) → _ ̇
 existence-of-unions₁ 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : (X → Ω _) → Ω _)
     → Σ \(B : X → Ω _)
             → (x : X) → (x ∈ B) ⇔ ∃ \(A : X → Ω _) → (A ∈ 𝓐) × (x ∈ A)

 existence-of-unions₂ : (𝓤 :  Universe) → 𝓤 ⁺⁺ ̇
 existence-of-unions₂ 𝓤 =
  (X : 𝓤 ̇ )
  (𝓐 : (X → Ω 𝓤) → Ω (𝓤 ⁺))
     → Σ \(B : X → Ω 𝓤)
             → (x : X) → (x ∈ B) ⇔ ∃ \(A : X → Ω 𝓤) → (A ∈ 𝓐) × (x ∈ A)

 existence-of-unions-agreement : existence-of-unions 𝓤 ≡ existence-of-unions₂ 𝓤
 existence-of-unions-agreement = refl _

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

  Top : (𝓤 : Universe) → 𝓤 ⁺⁺ ̇
  Top 𝓤 = Σ \(X : 𝓤 ̇ )
        → is-set X
        × Σ \(𝓞 : 𝓟𝓟 X)
        → full ∈ 𝓞
        × ((U V : 𝓟 X) → U ∈ 𝓞 → V ∈ 𝓞 → (U ∩ V) ∈ 𝓞)
        × ((𝓖 : 𝓟𝓟 X) → 𝓖 ⊆ 𝓞 → ⋃ 𝓖 ∈ 𝓞)

is-subsingleton-valued
 reflexive
 symmetric
 transitive
 is-equivalence-relation :

 {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇

is-subsingleton-valued  _≈_ = ∀ x y → is-subsingleton (x ≈ y)
reflexive               _≈_ = ∀ x → x ≈ x
symmetric               _≈_ = ∀ x y → x ≈ y → y ≈ x
transitive              _≈_ = ∀ x y z → x ≈ y → y ≈ z → x ≈ z

is-equivalence-relation _≈_ = is-subsingleton-valued _≈_
                            × reflexive _≈_
                            × symmetric _≈_
                            × transitive _≈_

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

 η-surjection : is-surjection η
 η-surjection = corestriction-surjection equiv-rel

 η-induction : (P : X/≈ → 𝓦 ̇ )
             → ((x' : X/≈) → is-subsingleton (P x'))
             → ((x : X) → P (η x))
             → (x' : X/≈) → P x'

 η-induction = surjection-induction η η-surjection

 η-equiv-equal : {x y : X} → x ≈ y → η x ≡ η y
 η-equiv-equal {x} {y} e =
  to-Σ-≡
    (hunapply (λ z → to-Σ-≡
                       (pe (≈p x z) (≈p y z) (≈t y x z (≈s x y e)) (≈t x y z e) ,
                        being-subsingleton-is-subsingleton hunapply _ _)) ,
     ∃-is-subsingleton _ _)

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
  open basic-arithmetic

  ≤-prop-valued : (x y : ℕ) → is-prop (x ≤ y)
  ≤-prop-valued 0 y               = 𝟙-is-subsingleton
  ≤-prop-valued (succ x) zero     = 𝟘-is-subsingleton
  ≤-prop-valued (succ x) (succ y) = ≤-prop-valued x y

  ≼-prop-valued : (x y : ℕ) → is-prop (x ≼ y)
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

positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)

𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚

lifttwo : is-univalent 𝓤₀ → is-univalent 𝓤₁ → (𝟚 ≡ 𝟚) ≡ Lift 𝓤₁ 𝟚

DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → ¬¬ P → P

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

