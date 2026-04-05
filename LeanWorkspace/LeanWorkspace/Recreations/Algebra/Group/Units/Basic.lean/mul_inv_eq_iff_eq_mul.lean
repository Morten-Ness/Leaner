import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b := ⟨fun h => by rw [← h, Units.inv_mul_cancel_right], fun h => by rw [h, Units.mul_inv_cancel_right]⟩

