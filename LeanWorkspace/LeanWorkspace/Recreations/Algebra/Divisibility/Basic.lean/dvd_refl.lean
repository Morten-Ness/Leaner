import Mathlib

variable {α : Type*}

variable [Monoid α] {a b c : α} {m n : ℕ}

theorem dvd_refl (a : α) : a ∣ a := Dvd.intro 1 (mul_one a)

