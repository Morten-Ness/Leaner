import Mathlib

variable {α β : Type*}

variable [Ring α] {a b : α}

theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b := dvd_add_left (dvd_refl a)

