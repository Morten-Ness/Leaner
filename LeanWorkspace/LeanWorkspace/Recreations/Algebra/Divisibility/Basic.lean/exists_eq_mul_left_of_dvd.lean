import Mathlib

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a := Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))

