import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x : M₀) ≠ 0 := nonZeroDivisors.ne_zero x.2

