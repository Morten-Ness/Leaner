import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mem_nonZeroDivisors_iff' :
    r ∈ M₀⁰ ↔ r ∈ nonZeroDivisorsLeft M₀ ∧ r ∈ nonZeroDivisorsRight M₀ := Iff.rfl

