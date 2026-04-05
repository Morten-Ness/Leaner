import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u := ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

