import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem powers_le_nonZeroDivisors_of_noZeroDivisors (hx : x ≠ 0) : Submonoid.powers x ≤ M₀⁰ := le_nonZeroDivisors_of_noZeroDivisors fun h ↦ hx (h.recOn fun _ ↦ eq_zero_of_pow_eq_zero)

