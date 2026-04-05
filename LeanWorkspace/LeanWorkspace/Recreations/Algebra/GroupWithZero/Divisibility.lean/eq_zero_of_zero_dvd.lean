import Mathlib

variable {α : Type*}

variable [SemigroupWithZero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 := Dvd.elim h fun c H' => H'.trans (zero_mul c)

