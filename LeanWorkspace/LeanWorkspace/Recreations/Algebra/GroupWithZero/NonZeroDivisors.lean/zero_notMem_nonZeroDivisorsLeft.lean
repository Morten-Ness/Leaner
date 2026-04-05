import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [Nontrivial M₀]

theorem zero_notMem_nonZeroDivisorsLeft : 0 ∉ nonZeroDivisorsLeft M₀ := fun h ↦ one_ne_zero <| h 1 <| zero_mul _

