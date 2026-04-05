import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c := by
  rw [mabs_lt, inv_lt_div_iff_lt_mul', div_lt_iff_lt_mul', and_comm, div_lt_iff_lt_mul']

