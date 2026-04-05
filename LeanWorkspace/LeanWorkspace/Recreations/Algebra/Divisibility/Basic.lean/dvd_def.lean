import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_def : a ∣ b ↔ ∃ c, b = a * c := Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def

