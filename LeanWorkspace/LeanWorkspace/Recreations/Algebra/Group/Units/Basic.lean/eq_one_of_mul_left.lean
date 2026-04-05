import Mathlib

variable {α : Type u}

variable [CommMonoid α]

variable [Subsingleton αˣ] {a b : α}

theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

