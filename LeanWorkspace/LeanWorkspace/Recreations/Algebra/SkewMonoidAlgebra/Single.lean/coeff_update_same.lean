import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem coeff_update_same : (f.update a b).coeff a = b := by
  classical
  rw [SkewMonoidAlgebra.coeff_update_apply f, if_pos rfl]

