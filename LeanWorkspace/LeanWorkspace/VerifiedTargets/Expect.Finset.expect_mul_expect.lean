import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semiring M] [Module ℚ≥0 M]

theorem expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (s : Finset ι)
    (t : Finset κ) (f : ι → M) (g : κ → M) :
    (𝔼 i ∈ s, f i) * 𝔼 j ∈ t, g j = 𝔼 i ∈ s, 𝔼 j ∈ t, f i * g j := by
  simp_rw [Finset.expect_mul, Finset.mul_expect]

