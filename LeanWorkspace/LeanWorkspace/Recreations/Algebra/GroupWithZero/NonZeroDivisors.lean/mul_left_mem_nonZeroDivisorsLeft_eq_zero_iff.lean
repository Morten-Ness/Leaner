import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff (hr : r ∈ nonZeroDivisorsLeft M₀) :
    r * x = 0 ↔ x = 0 := ⟨hr _, by simp +contextual⟩

