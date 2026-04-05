import Mathlib

variable {α β : Type*}

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  rw [sub_eq_add_neg, dvd_add_right h, dvd_neg]

