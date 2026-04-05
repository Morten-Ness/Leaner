import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

