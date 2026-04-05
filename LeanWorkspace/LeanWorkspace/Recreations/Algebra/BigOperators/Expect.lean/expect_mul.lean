import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semiring M] [Module ℚ≥0 M]

theorem expect_mul [IsScalarTower ℚ≥0 M M] (s : Finset ι) (f : ι → M) (a : M) :
    (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by rw [expect, expect, smul_mul_assoc, sum_mul]

