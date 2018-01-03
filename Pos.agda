module Pos where

open import Category
open import Prelude.Function
open import Prelude.Product
open import Prelude.Equality as Eq hiding (trans)

-- Partially ordered set
record Poset : Set₁ where
  field
    A     : Set
  field
    _<=_  : A → A → Set 
    reflx  : ∀ (a : A) → a <= a
    asymt  : ∀ (a b : A) → a <= b → b <= a → a ≡ b
    trans : ∀ {a b c : A} → a <= b → b <= c → a <= c

record Poset' :  Set₁ where
  field
     P : Poset
  module P = Poset P
  field
    _≈_ : ∀ {a b : P.A} → (f : a P.<= b) → (g : a P.<= b) → f ≡ g
    
-- Monotonic function
record _⇒_ (P Q : Poset) : Set where
  private
    module P = Poset P
    module Q = Poset Q
  field
    m        : P.A → Q.A
    monotone : ∀ (a a' : P.A) → a P.<= a' → m a Q.<= m a'

-- composing monotones gives a monotone
_∙_ : {A B C : Poset} → B ⇒ C → A ⇒ B → A ⇒ C
g ∙ f = record {
  m = (_⇒_.m g) ∘ (_⇒_.m f) ;
  monotone = λ a a' a<=a' →
    let f-m = _⇒_.m f 
        g-m = _⇒_.m g in
    _⇒_.monotone g (f-m a) (f-m a') (_⇒_.monotone f a a' a<=a') }

Id : (A : Poset) → A ⇒ A
Id = λ A → record { m = id ; monotone = λ a a' a<=a' → a<=a' }

-- category of posets
Pos : Category (lsuc lzero) lzero
Pos = record {
  Object = Poset ;
  _⇒_ = _⇒_ ;
  _∙_ = _∙_ ;
  Id = Id ;
  assoc = λ A B C D f g h → refl ;
  ident = λ A B f → refl , refl }

-- a poset as a category
PosetAsCategory : Poset' → Category lzero lzero
PosetAsCategory P' =
  let
    module P' = Poset' P'
    module P = P'.P
   in record {
  Object = P.A ;
  _⇒_ = λ a b → a P.<= b ;
  _∙_ = λ {A} {B} {C} B<=C A<=B → P.trans A<=B B<=C ;
  Id = P.reflx ;
  assoc = λ A B C D f g h →  (P.trans (P.trans f g) h) P'.≈ (P.trans f (P.trans g h)) ;
  ident = λ A B f → ((P.trans (P.reflx A)) f P'.≈ f) , f P'.≈ P.trans f (P.reflx B) }
