import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det := @isUnit_of_invertible _ _ _ (Matrix.detInvertibleOfLeftInverse _ _ h)

