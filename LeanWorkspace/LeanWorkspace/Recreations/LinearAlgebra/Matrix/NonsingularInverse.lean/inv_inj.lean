import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

variable {C : Matrix n n α}

theorem inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B := by
  refine Matrix.left_inv_eq_left_inv (Matrix.mul_nonsing_inv _ h') ?_
  rw [h]
  refine Matrix.mul_nonsing_inv _ ?_
  rwa [← Matrix.isUnit_nonsing_inv_det_iff, ← h, Matrix.isUnit_nonsing_inv_det_iff]

