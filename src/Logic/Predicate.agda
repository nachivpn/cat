module Logic.Predicate where

open import Level

data ∃ {a b} (A : Set a) (P : A → Set b) : Set (a ⊔ b) where
 <_,_> : (a : A) → P a → ∃ A P

∃-elim : {A : Set} → {P : A → Set} → {Q : Set}
  → ((a : A) → P a → Q) → ∃ A P → Q
∃-elim f < a , p > = f a p
  
