import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_mul_right (a b : α) : a ∣ a * b := Dvd.intro b rfl

