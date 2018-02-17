module Lemma.AbstractObject where


open import Level
open import Category


module Core {o a e} {C : Category o a e} where

  open import Iso
  open import InitTerm
  open import Data.Product
  
  open Category.Category C
  open InitTerm.Core C
  open Iso.Core C
  open iso
  
  initialsUnique : ∀ {A B} → initial A → initial B → A ≅ B
  initialsUnique {A} {B} (init A2) (init B2) = 
    record {
      ∃iso = witness (A2 B) ,
        record {
          inv = witness (B2 A) ;
          bnf = trans isEq (sym isEq (!A2A tt)) (!A2A tt); 
          fnb = trans isEq (sym isEq (!B2B tt)) (!B2B tt) } }
    where
    !A2A = ump (A2 A)
    !B2B = ump (B2 B)
     
  terminalsUnique : ∀ {A B} → terminal A → terminal B → A ≅ B
  terminalsUnique {A} {B} (term 2A) (term 2B) =
    record {
      ∃iso = witness (2B A) ,
      record {
        inv = witness (2A B) ;
        bnf = trans isEq (sym isEq (!A2A tt)) (!A2A tt) ;
        fnb = trans isEq (sym isEq (!B2B tt)) (!B2B tt)} }
    where
    !A2A = ump (2A A)
    !B2B = ump (2B B)
