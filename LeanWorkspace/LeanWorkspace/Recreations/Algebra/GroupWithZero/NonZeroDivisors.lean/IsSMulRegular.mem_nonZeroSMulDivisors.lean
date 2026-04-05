import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsSMulRegular.mem_nonZeroSMulDivisors {M : Type*} [Zero M] [MulActionWithZero M₀ M] {m₀ : M₀}
    (h : IsSMulRegular M m₀) : m₀ ∈ nonZeroSMulDivisors M₀ M := fun _ ↦ h.right_eq_zero_of_smul

