import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem one_dvd (a : α) : 1 ∣ a := Dvd.intro a (one_mul a)

