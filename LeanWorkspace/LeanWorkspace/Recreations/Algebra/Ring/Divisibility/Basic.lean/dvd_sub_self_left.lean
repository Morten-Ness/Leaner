import Mathlib

variable {α β : Type*}

variable [Ring α] {a b : α}

theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b := dvd_sub_right dvd_rfl

