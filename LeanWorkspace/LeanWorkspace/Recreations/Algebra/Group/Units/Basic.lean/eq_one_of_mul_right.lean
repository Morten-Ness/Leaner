import Mathlib

variable {α : Type u}

variable [CommMonoid α]

variable [Subsingleton αˣ] {a b : α}

theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 := congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

