import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰ := fun h ↦ zero_notMem_nonZeroDivisorsLeft h.1

