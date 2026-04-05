import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_cases (a : G) : |a|ₘ = a ∧ 1 ≤ a ∨ |a|ₘ = a⁻¹ ∧ a < 1 := by
  cases le_or_gt 1 a <;> simp [*, le_of_lt]

