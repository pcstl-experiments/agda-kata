{-# OPTIONS --copattern --safe --no-sized-types --guardedness #-}
module Copattern where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream public

record _==_ {A : Set} (x : Stream A) (y : Stream A) : Set where
  coinductive
  field
    refl-head : head x ≡ head y
    refl-tail : tail x == tail y
open _==_ public

module Introduction where
  ones : Stream ℕ
  head ones = suc zero
  tail ones = ones

  repeat : {A : Set} → A → Stream A
  head (repeat a) = a
  tail (repeat a) = repeat a

  even : ∀ {A} → Stream A → Stream A
  head (even stream) = head stream
  tail (even stream) = even (tail (tail stream))

  odd : ∀ {A} → Stream A → Stream A
  odd stream = even (tail stream)

module Bisimulation where
  open Introduction

  refl′ : ∀ {A} → (a : Stream A) → a == a
  refl-head (refl′ a) = refl
  refl-tail (refl′ a) = refl′ (tail a)

  oddEven : ∀ {A} → (a : Stream A) → odd a == even (tail a)
  refl-head (oddEven a) = refl
  refl-tail (oddEven a) = refl′ (odd (tail (tail a)))
  

module Merge where
  open Bisimulation
  open Introduction

  merge : ∀ {A} → Stream A → Stream A → Stream A
  head (merge a b) = head a
  tail (merge a b) = merge b (tail a)
  
  moe : ∀ {A} → (a : Stream A) → merge (even a) (odd a) == a
  refl-head (moe a) = refl
  refl-tail (moe a) = moe (tail a)
