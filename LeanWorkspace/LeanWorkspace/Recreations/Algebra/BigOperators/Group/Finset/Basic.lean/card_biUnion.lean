import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem card_biUnion [DecidableEq M] {t : ι → Finset M} (h : (s : Set ι).PairwiseDisjoint t) :
    #(s.biUnion t) = ∑ u ∈ s, #(t u) := by simpa using sum_biUnion h (M := ℕ) (f := 1)

