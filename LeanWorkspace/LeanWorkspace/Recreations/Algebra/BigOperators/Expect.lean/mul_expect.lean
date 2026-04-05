import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semiring M] [Module ℚ≥0 M]

theorem mul_expect [SMulCommClass ℚ≥0 M M] (s : Finset ι) (f : ι → M) (a : M) :
    a * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a * f i := by rw [expect, expect, mul_smul_comm, mul_sum]

