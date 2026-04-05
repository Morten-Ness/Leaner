import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_le_iff : |a / b|ₘ ≤ c ↔ a / b ≤ c ∧ b / a ≤ c := by
  rw [mabs_le, inv_le_div_iff_le_mul, div_le_iff_le_mul', and_comm, div_le_iff_le_mul']

