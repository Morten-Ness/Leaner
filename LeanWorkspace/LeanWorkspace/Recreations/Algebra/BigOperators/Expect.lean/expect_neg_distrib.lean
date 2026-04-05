import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommGroup M] [Module ℚ≥0 M]

theorem expect_neg_distrib (s : Finset ι) (f : ι → M) : 𝔼 i ∈ s, -f i = -𝔼 i ∈ s, f i := by
  simp [expect]

