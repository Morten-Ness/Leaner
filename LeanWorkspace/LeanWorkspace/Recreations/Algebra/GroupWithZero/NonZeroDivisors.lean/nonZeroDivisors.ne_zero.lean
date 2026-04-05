import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem nonZeroDivisors.ne_zero (hx : x ∈ M₀⁰) : x ≠ 0 := ne_of_mem_of_not_mem hx zero_notMem_nonZeroDivisors

