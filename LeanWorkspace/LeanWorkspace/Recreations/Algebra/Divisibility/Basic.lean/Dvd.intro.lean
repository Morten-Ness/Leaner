import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b := Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro

