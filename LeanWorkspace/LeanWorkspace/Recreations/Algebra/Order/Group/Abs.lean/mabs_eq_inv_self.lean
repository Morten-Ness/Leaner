import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a ≤ 1 := by
  rw [mabs_eq_max_inv, max_eq_right_iff, le_inv_self_iff]

