import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (a b : αˣ) {u : αˣ}

theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, Units.mul_inv u]

