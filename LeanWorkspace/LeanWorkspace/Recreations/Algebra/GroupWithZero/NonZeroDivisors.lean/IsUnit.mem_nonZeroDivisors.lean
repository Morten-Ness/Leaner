import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem IsUnit.mem_nonZeroDivisors (hx : IsUnit x) : x ∈ M₀⁰ := ⟨fun _ ↦ hx.mul_right_eq_zero.mp, fun _ ↦ hx.mul_left_eq_zero.mp⟩

