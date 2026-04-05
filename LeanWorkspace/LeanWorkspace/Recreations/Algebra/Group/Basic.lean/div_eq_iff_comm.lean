import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_iff_comm : a / b = c ↔ a / c = b := by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]

