import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mem_nonZeroDivisors_iff :
    r ∈ M₀⁰ ↔ (∀ x, r * x = 0 → x = 0) ∧ ∀ x, x * r = 0 → x = 0 := Iff.rfl

