import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem coeff_update_ne (h : a' ≠ a) : (f.update a b).coeff a' = f.coeff a' := by
  classical
  rw [SkewMonoidAlgebra.coeff_update_apply f, if_neg h]

