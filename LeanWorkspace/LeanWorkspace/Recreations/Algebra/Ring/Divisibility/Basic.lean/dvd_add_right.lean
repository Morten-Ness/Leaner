import Mathlib

variable {α β : Type*}

variable [NonUnitalRing α] {a b c : α}

theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm]; exact dvd_add_left h

