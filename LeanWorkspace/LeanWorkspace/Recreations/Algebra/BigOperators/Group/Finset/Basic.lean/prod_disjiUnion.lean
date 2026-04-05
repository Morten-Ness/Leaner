import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_disjiUnion (s : Finset κ) (t : κ → Finset ι) (h) :
    ∏ x ∈ s.disjiUnion t h, f x = ∏ i ∈ s, ∏ x ∈ t i, f x := by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

