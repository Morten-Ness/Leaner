import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a := calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

