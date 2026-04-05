import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x := Units.mul_left_inj u.symm.trans <| by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

