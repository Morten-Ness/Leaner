import Mathlib

variable {α β : Type*}

variable [NonUnitalRing α] {a b c : α}

theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c, dvd_add_right h]

