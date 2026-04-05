import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

