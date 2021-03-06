## Activity Journal

(reverse chronological order)

### 20/02/18
* Got stuck trying to prove ump of co-products for STLC category (using propositional equality)
* The morphism - which must be proved to be unique - `Either A B ⇒ Z` is defined using pattern matching as:
    ```Haskell
    u : ∀ {A B Z} → (z₁ : A ⇒ Z) (z₂ : B ⇒ Z) → Either A B ⇒ Z
    u z₁ z₂ (left x) = z₁ x
    u z₁ z₂ (right x) = z₂ x 
    ``` 
  proving the uniqueness of `u` requires a proof of `u (y ∙ left) (y ∙ right) ≈ y`, where y is another morphism such that `y ∙ left ≈ z₁` and `y ∙ right ≈ z₂`. This appears impossible to do using propositional equality (needs more clarity on why).
* Need to use functional extensionality to solve this problem

### 10/02/18
* added product and natural transformation constructions
* closed open goals in Op category, removed use of flip (makes goals look ugly)
* proof for "products are unique upto iso" was surprisingly a little tricky to close; took some time to wrap my head around the representation of universality properties, but turned out to be rather simple after the "aha" moment of realizing that `witness-pr` was needed for discharging the properties of the universal object
* going to do a few more category theory proofs before coming back to ground with implementation of concrete instances

### 03/02/18
* added split-epi and split-mono
* added `substl` and `substr` as sugar with implicit parameters for `congr` and `congl` (respectively).
* Need to add a "sugar lemma" for expanding and contracting on Id

### 30/01/18
* Slowly stepping into "Abstract structures" chapter
* Proofs written using `Relation.Binary.SetoidReasoning` are stunning! Totally worth it!
* Added mono- & epi- morphisms

### 27/01/18
* Added first pure category theory proof today! Inverses of an isomorphism are indeed unique!
* Used setoid equational reasoning library for proof, quite convenient
* need to make arguments of id-l and id-r implicit, they are quite cumbersome to use in proofs now (done!)
* how to avoid giving "isEq" as argument to sym/trans/refl proofs?

### 20/01/18

* From a discussion with Jannis on Thursday for solving the problem of defining equality of functors (say `F,G : C -> D`), one suggested option to circumvent the mismatch in types is to define `F₀` equality as isomorphism, i.e., `iso : {x} -> F.F₀ x ≅ G.F₀ x`, and then use this to define equality of `F₁` as `(F.F₁ f) D.≈ (back iso D.∘ G.F₁ f D.∘ forth iso)`. 
* Looking closer at the suggested solution reveals that this is indeed a result of the naturality conditions which arise from a natural isomorphism between `F` and `G`! Hence, natural isomorphism appears promising as an option to define `≈` of functors.
* Added product category construction and isomorphism

### 13/01/18

* Natural isomorphism between functors maybe suitable for `≈` of functors. Need to come back to this (Cat) much later!
* Tried defining equality of functors (morphisms in Cat) today. One option is the equality of the underlying object and arrow maps. Functional extensionality could be an option. But this gets tricky as `F.F₀ x != G.F₀ x` and hence `(F.F₀ A) D.⇒ (F.F₀ B)` and `(G.F₀ A) D.⇒ (G.F₀ B)` are of different types, and `D.≈` cannot be used to define the equality of these morphisms of different types. How does one define a "heterogenous" equality between such morphisms?

### 12/01/18
  
* Tried replacing `congl` and `congr` with substitution. It is possible to define congruence in terms of substitution, but "native" `subst` is difficult (not possible?) to prove in some cases that are not propositional equality (Eg: PosetAsCategory); so discarded changes. Alternatively, one could define equality such that subst is available (as a constructor, for example), or simply postulate it.
* Added cong (left and right composition); will be needed for purely categorical proofs (eg: epi, mono etc)

### Older tweets

* Closed open goals for category of monoids. Defined equality as the equality of the functions underlying the homomorphisms. Whether this truly suffices needs more consideration
* Added the monoid category today. Coming up next: the category of monoids. Stay tuned!
* Closed open goals for unit laws in Rel, Woohooooo! Rel is indeed a category, I assure you!!
* Reason for choosing logical equivalence is because composition is defined as a proof of "there exists". Hence, proving associativity of composition is basically showing the equivalence of two such proofs.
* Equivalence of morphisms in the Rel category is a bit tricky. Adopting "logical equivalence" (i.e., iff or two way implication) has worked well for proving associativity of composition. Identity laws are yet to be proved
* For meta categories, on the other hand, since the exact equivalence relation is not available, we need to ensure that the binary "equivalence" relation is indeed an equivalence relation by requiring a proof of equivalence properties. Added this today!
* For concrete categories, once the equivalence relation is set, the proofs come about easily because we have the equivalence properties (refl, sym, trans) of the exact instance of equality
* The problem of equality unveils itself even when dealing with simple concrete categories like Pos, and becomes profound when dealing with meta-categories such as Cat
* Slowly making progress on embedding category theoretic concepts in Agda. Propositional equality as a generic solution to equality of morphisms is limiting, so switched to context dependant equality
