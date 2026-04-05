import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem update_zero_eq_erase : f.update a 0 = f.erase a := by
  classical ext; simp [SkewMonoidAlgebra.coeff_update_apply, SkewMonoidAlgebra.coeff_erase_apply]

