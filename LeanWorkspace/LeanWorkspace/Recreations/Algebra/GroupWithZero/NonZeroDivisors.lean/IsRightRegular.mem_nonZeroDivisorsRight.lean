import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsRightRegular.mem_nonZeroDivisorsRight (h : IsRightRegular r) :
    r ∈ nonZeroDivisorsRight M₀ := fun _x hx ↦ h.mul_right_eq_zero_iff.mp hx

