import Mathlib

variable {α β : Type*}

variable [Ring α] {a b : α}

theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b := dvd_sub_left dvd_rfl

