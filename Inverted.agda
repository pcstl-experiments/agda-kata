module Inverted where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties

suc-≡ : (a b : ℕ) → suc a ≡ suc b → a ≡ b
suc-≡ zero    zero refl     = refl
suc-≡ (suc a) (suc .a) refl = refl

invert : (a b : ℕ) → a + a ≡ b + b → a ≡ b
invert zero zero refl = refl
invert (suc a′) (suc b′) a+a≡b+b =
  let a+suc-a≡b+suc-b = suc-≡ (a′ + suc a′) (b′ + suc b′) a+a≡b+b
      a+suc-a≡suc-b+b = trans a+suc-a≡b+suc-b (+-suc b′ b′)
      suc-a+a≡suc-b+b = sym (trans (sym a+suc-a≡suc-b+b) (+-suc a′ a′))
      a+a≡b+b = suc-≡ (a′ + a′) (b′ + b′) suc-a+a≡suc-b+b
  in cong suc (invert a′ b′ a+a≡b+b)
  
