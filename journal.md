## Activity Journal

(reverse chronological order)

### 13/01/18

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
