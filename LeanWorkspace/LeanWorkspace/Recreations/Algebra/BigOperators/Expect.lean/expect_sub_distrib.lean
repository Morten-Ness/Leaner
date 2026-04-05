import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommGroup M] [Module ℚ≥0 M]

theorem expect_sub_distrib (s : Finset ι) (f g : ι → M) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  simp only [expect, sum_sub_distrib, smul_sub]

