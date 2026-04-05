import Mathlib

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem mem_nonZeroDivisorsLeft_iff : x ∈ nonZeroDivisorsLeft M₀ ↔ ∀ y, x * y = 0 → y = 0 := .rfl

