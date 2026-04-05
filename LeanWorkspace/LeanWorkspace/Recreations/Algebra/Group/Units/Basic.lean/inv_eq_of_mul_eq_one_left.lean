import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a := calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, Units.mul_inv_cancel_right]

