import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem finset_prod_mk {p : Finset ι} {f : ι → M} :
    (∏ i ∈ p, Associates.mk (f i)) = Associates.mk (∏ i ∈ p, f i) := by
  classical
  refine Finset.induction_on p ?_ ?_
  · simp
  · intro a s ha hs
    simp [ha, hs, Associates.mk_mul_mk]
