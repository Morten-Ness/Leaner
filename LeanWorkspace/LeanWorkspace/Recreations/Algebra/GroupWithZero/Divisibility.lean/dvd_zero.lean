import Mathlib

variable {α : Type*}

variable [SemigroupWithZero α] {a : α}

theorem dvd_zero (a : α) : a ∣ 0 := Dvd.intro 0 (by simp)

