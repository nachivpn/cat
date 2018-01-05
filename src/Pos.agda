module Pos where

open import Category
open import Prelude.Function
open import Prelude.Product
open import Relation.Binary hiding (_⇒_ ; Poset)
open import Relation.Binary.PropositionalEquality as Eq hiding (trans)
open import Prelude.Unit

-- Partially ordered set
record Poset : Set₁ where
  field
    A     : Set
    _<=_  : A → A → Set 
    reflx  : ∀ (a : A) → a <= a
    asymt  : ∀ (a b : A) → a <= b → b <= a → a ≡ b
    trans : ∀ {a b c : A} → a <= b → b <= c → a <= c
  -- Constructions of <= (proofs) are unique
  -- This aids the "an arrow per <= relation"
  -- construction in PosetAsCategory
  _≈_ : {a b : A} → (f g : a <= b) → Set
  _≈_ f g = ⊤
  isEq : {a b : A} → IsEquivalence (_≈_ {a} {b})
  isEq = record { refl = tt ; sym = λ {i} {j} _ → tt ; trans = λ _ _ → tt }

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
Pos : Category (lsuc lzero) lzero lzero
Pos = record {
  Object = Poset ;
  _⇒_ = _⇒_ ;
  _∙_ = _∙_ ;
  Id = Id ;
  _≈_ = _≡_ ;
  isEq = isEquivalence ;
  assoc = λ A B C D f g h → refl ;
  id-l = λ A B f → refl ;
  id-r = λ A B f → refl }

-- a poset as a category
PosetAsCategory : Poset → Category lzero lzero lzero
PosetAsCategory P =
  let
    module P = Poset P
  in record {
  Object = P.A ;
  _⇒_ = λ a b → a P.<= b ;
  _∙_ = λ {a} {b} {c} b<=c a<=b → P.trans a<=b b<=c ;
  Id = P.reflx ;
   _≈_ = P._≈_ ; -- arrows are unique by definition
  isEq = P.isEq ;
  assoc = λ A B C D f g h → tt ; 
  id-l = λ A B f → tt ;
  id-r = λ A B f → tt }
