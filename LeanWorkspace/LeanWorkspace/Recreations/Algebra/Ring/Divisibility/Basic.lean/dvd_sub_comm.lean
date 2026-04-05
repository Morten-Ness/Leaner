import Mathlib

variable {α β : Type*}

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg, neg_sub]

