import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsLeftRegular.mem_nonZeroDivisorsLeft (h : IsLeftRegular r) :
    r ∈ nonZeroDivisorsLeft M₀ := fun _x hx ↦ h.mul_left_eq_zero_iff.mp hx

