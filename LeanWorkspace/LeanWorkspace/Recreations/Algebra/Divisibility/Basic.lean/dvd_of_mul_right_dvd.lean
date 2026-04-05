import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c := (dvd_mul_right a b).trans h

