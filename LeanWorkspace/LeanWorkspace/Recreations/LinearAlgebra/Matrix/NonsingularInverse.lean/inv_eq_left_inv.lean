import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B := letI := invertibleOfLeftInverse _ _ h
  Matrix.invOf_eq_nonsing_inv A ▸ invOf_eq_left_inv h

