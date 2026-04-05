import Mathlib

variable {α : Type u}

theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟(u : α) = ↑u⁻¹ := invOf_eq_right_inv u.mul_inv

