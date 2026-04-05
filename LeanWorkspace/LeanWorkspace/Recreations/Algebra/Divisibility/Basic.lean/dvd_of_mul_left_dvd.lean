import Mathlib

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c := Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])

