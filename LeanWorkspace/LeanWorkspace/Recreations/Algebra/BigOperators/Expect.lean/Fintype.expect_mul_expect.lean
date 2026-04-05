import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [Semiring M] [Module ℚ≥0 M]

theorem expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (f : ι → M)
    (g : κ → M) : (𝔼 i, f i) * 𝔼 j, g j = 𝔼 i, 𝔼 j, f i * g j := Finset.expect_mul_expect ..

