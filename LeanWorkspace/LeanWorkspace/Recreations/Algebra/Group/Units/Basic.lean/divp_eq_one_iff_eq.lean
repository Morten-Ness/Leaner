import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u := (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]

