import Mathlib

variable {α : Type*}

theorem mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsCancelMulZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b := exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]

