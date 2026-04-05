import Mathlib

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem mem_nonZeroDivisorsRight_iff : x ∈ nonZeroDivisorsRight M₀ ↔ ∀ y, y * x = 0 → y = 0 := .rfl

