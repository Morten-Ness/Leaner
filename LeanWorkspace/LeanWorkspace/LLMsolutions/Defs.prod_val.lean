import Mathlib

variable {ι κ M N G α : Type*}

theorem prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.prod id := by
  classical
  refine Finset.induction_on s ?h ?step
  · simp
  · intro a s ha hs
    simp [Finset.prod_insert, ha, hs]
