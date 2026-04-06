import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem prod_sum {ι : Type*} [CommMonoid M] (f : ι → Multiset M) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by
  classical
  refine Finset.induction_on s ?h ?step
  · simp
  · intro a s ha ih
    simp [ha, ih, Multiset.prod_add]
