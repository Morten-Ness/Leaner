import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem isSMulRegular_iff_mem_nonZeroSMulDivisors {M : Type*} [AddGroup M] [DistribMulAction M₀ M]
    {m₀ : M₀} : IsSMulRegular M m₀ ↔ m₀ ∈ nonZeroSMulDivisors M₀ M := isSMulRegular_iff_right_eq_zero_of_smul

