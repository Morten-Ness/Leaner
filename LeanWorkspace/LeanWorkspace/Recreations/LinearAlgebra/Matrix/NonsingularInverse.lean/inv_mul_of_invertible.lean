import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_mul_of_invertible [Invertible A] : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (Matrix.isUnit_det_of_invertible A)

