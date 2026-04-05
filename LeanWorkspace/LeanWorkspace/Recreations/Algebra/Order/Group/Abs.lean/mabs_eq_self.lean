import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_eq_self : |a|ₘ = a ↔ 1 ≤ a := by
  rw [mabs_eq_max_inv, max_eq_left_iff, inv_le_self_iff]

