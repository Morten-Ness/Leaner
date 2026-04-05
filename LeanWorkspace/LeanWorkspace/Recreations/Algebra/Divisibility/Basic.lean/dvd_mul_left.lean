import Mathlib

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_mul_left (a b : α) : a ∣ b * a := Dvd.intro b (mul_comm a b)

