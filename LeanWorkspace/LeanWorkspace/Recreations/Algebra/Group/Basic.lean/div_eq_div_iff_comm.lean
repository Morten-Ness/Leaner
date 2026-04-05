import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c := inv_inj.symm.trans <| by simp only [inv_div]

