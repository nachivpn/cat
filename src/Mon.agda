module Mon where

open import Category
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Prelude.Function
open import Data.Nat
open import Data.Nat.Properties

record Monoid : Set₁ where
  field
    Car    : Set
    _∙_    : Car → Car → Car
    u      : Car
    assoc  : ∀ a b c → a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
    unit-l : ∀ x → x ∙ u ≡ x
    unit-r : ∀ x → x ≡ u ∙ x

-- Monoid homomorphism
record _⇒_ (M N : Monoid) : Set where
  private
    module M = Monoid M
    module N = Monoid N
  field
    -- function for the underlying set
    f      : M.Car → N.Car
    -- preservation of composition, i.e, "structural preservation"
    pres-∙ : ∀ {m₁ m₂ : M.Car} → f (m₁ M.∙ m₂) ≡ f m₁ N.∙ f m₂
    -- preservation of unit
    pres-u : f M.u ≡ N.u

_∙_ : ∀ {X Y Z} (g : Y ⇒ Z) (f : X ⇒ Y) → X ⇒ Z
g ∙ f = let
  module f = _⇒_ f
  module g = _⇒_ g in record {
    f =  g.f ∘ f.f ;
    pres-∙ = trans (cong g.f f.pres-∙) g.pres-∙ ;
    pres-u = trans (cong g.f f.pres-u) g.pres-u }

Id : (A : Monoid) → A ⇒ A
Id A = record { f = id ; pres-∙ = refl ; pres-u = refl }

data _≈_ {M N : Monoid} (F G : M ⇒ N) : Set where
  eq : let
    module F = _⇒_ F
    module G = _⇒_ G
   in (∀ x → F.f x ≡ G.f x) → F ≈ G

MonoidCategory : Monoid → Category lzero lzero lzero
MonoidCategory M = let module M = Monoid M in record
                { Object = ⊤
                ; _⇒_ = λ _ _ → M.Car
                ; _∙_ = M._∙_
                ; Id = λ _ → M.u
                ; _≈_ = _≡_
                ; isEq = isEquivalence
                ; assoc = λ _ _ _ _ f g h → M.assoc h g f
                ; id-l = λ _ _ f → M.unit-l f
                ; id-r = λ _ _ f → M.unit-r f
                ; congl = λ x y x≡y f → cong (M._∙_ f) x≡y
                ; congr = λ x y x≡y f → cong (flip M._∙_ f) x≡y
                }


refl' : ∀ {M N : Monoid} {F : M ⇒ N} → F ≈ F
refl' = eq λ _ → refl

sym' : ∀ {M N : Monoid} {F G : M ⇒ N} → F ≈ G → G ≈ F
sym' (eq p) = eq (sym ∘ p)

trans' : ∀ {A B : Monoid} {F G H : A ⇒ B} → F ≈ G → G ≈ H → F ≈ H
trans' (eq p) (eq q) = eq λ x → trans (p x) (q x)

congl : {A B C : Monoid} (g h : A ⇒ B) → g ≈ h → (f : B ⇒ C) → (f ∙ g) ≈ (f ∙ h)
congl g h (eq p) f = let module f = _⇒_ f in eq λ x → cong f.f (p x)

congr : {A B C : Monoid} (g h : B ⇒ C) → g ≈ h → (f : A ⇒ B) → (g ∙ f) ≈ (h ∙ f)
congr g h (eq p) f = let module f = _⇒_ f in eq λ x → p (f.f x)

Mon : Category (lsuc lzero) lzero lzero
Mon = record
                { Object = Monoid
                ; _⇒_ = _⇒_
                ; _∙_ = _∙_
                ; Id = Id
                ; _≈_ = _≈_
                ; isEq = record {
                  refl = refl' ;
                  sym = sym' ;
                  trans = trans' }
                ; assoc = λ A B C D f g h → eq λ _ → refl
                ; id-l = λ A B f → eq λ _ → refl
                ; id-r = λ A B f → eq λ _ → refl
                ; congl = congl
                ; congr = congr
                }

private
  -- Sample monoid
  ⟨N,+,0⟩ : Monoid
  ⟨N,+,0⟩ = record{
    Car = ℕ ;
    _∙_ = _+_ ;
    u = zero ;
    assoc = λ a b c → sym (+-assoc a b c) ;
    unit-l = λ x → +-identityʳ x ;
    unit-r = λ x → +-identityˡ x }

  ⟨N,+,0⟩-cat : Category lzero lzero lzero
  ⟨N,+,0⟩-cat = MonoidCategory ⟨N,+,0⟩
