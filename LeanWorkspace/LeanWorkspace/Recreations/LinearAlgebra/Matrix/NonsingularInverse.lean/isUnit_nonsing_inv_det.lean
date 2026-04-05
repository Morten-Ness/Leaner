import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem isUnit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det := .of_mul_eq_one _ (A.det_nonsing_inv_mul_det h)

