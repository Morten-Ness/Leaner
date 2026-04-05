import Mathlib

variable {α : Type*}

theorem mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCancelMulZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c := exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]

