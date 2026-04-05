import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem mul_inv_of_invertible [Invertible A] : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_invertible A)

