import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_one_iff [Subsingleton Mˣ] : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    simp [ha, hs]
