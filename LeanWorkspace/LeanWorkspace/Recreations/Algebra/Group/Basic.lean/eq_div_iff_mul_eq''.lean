import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

