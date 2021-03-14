{-# OPTIONS --safe #-}
module RevRev where

open import Relation.Binary.PropositionalEquality
open import Data.List

rev : ∀ {ℓ} {A : Set ℓ} → List A → List A
rev []       = []
rev (x ∷ xs) = rev xs ++ x ∷ []

rev-append-single : ∀ {ℓ} {A : Set ℓ} (xs : List A) (x : A) → rev (xs ++ x ∷ []) ≡ (x ∷ (rev xs))
rev-append-single [] x = refl
rev-append-single (x₁ ∷ xs) x
  rewrite rev-append-single xs x₁
        | rev-append-single xs x = refl

rev-rev : ∀ {ℓ} {A : Set ℓ} (a : List A) → rev (rev a) ≡ a
rev-rev []       = refl
rev-rev (x ∷ xs)
  rewrite rev-append-single xs x
        | rev-append-single (rev xs) x
        | rev-rev xs = refl
