import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem le_nonZeroDivisors_of_noZeroDivisors {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) :
    S ≤ M₀⁰ := fun _ hx ↦
  mem_nonZeroDivisors_of_ne_zero <| by rintro rfl; exact hS hx

