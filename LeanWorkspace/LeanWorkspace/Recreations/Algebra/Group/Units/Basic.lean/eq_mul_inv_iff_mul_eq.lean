import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b := ⟨fun h => by rw [h, Units.inv_mul_cancel_right], fun h => by rw [← h, Units.mul_inv_cancel_right]⟩

