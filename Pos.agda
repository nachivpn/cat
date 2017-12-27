module Pos where

open import Category

record Eq (A : Set) : Set₁ where
  field
    _≅_ : A → A → Set

record Poset : Set₁ where
  field
    A     : Set
    eq    : Eq A
  open Eq eq public
  field
    _<=_  : A → A → Set 
    reflx : ∀ (a : A) → a <= a
    asymt : ∀ (a b : A) → a <= b → b <= a → a ≅ b
    trans : ∀ (a b c : A) → a <= b → b <= c → a <= c

record _⇒_ (P Q : Poset) : Set where
  -- TODO!

Pos : Category (lsuc lzero) lzero
Pos = record {
        Object = Poset ;
        _⇒_ = _⇒_ ;
        _∙_ = {!!} ;
        Id = {!!} ;
        assoc = {!!} ;
        ident = {!!} }
