import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c := h

