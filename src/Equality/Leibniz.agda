module Equality.Leibniz where

open import Level
open import Data.Product

data _≈_ {a p} {A : Set a} (x y : A) : Set (suc p ⊔ a) where
  eq : ∀ (P : A → Set p) → (P x → P y) → (P y → P x) → x ≈ y
