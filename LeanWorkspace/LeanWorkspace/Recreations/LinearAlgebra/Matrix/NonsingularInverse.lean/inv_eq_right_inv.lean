import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B := Matrix.inv_eq_left_inv (mul_eq_one_comm.2 h)

