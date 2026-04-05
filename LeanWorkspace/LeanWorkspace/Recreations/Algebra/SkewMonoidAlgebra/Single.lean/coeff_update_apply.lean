import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem coeff_update_apply [DecidableEq α] :
    (f.update a b).coeff a' = if a' = a then b else f.coeff a' := by
  rw [SkewMonoidAlgebra.coeff_update, Function.update_apply]

