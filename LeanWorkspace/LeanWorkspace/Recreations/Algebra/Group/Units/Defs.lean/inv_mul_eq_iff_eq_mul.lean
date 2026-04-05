import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c := ⟨fun h => by rw [← h, Units.mul_inv_cancel_left], fun h => by rw [h, Units.inv_mul_cancel_left]⟩

