import Mathlib

variable {α β : Type*}

variable [Ring α] {a b : α}

theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b := dvd_add_right (dvd_refl a)

