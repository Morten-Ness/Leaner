import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ → Finset ι}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by
  rw [← disjiUnion_eq_biUnion _ _ hs, Finset.prod_disjiUnion]

