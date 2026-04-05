import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem isUnit_le_nonZeroDivisors : IsUnit.submonoid M₀ ≤ M₀⁰ := fun _ ↦ (·.mem_nonZeroDivisors)

