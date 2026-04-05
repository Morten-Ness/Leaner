import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, Units.inv_mul u]

