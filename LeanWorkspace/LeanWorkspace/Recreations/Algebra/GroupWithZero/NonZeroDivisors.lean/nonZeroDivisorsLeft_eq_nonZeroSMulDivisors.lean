import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem nonZeroDivisorsLeft_eq_nonZeroSMulDivisors :
    nonZeroDivisorsLeft M₀ = nonZeroSMulDivisors M₀ M₀ := rfl

