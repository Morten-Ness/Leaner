import Mathlib

variable {α β : Type*}

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

