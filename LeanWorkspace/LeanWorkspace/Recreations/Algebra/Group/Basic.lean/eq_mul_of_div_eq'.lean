import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

