import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

theorem coeff_erase_same : (f.erase a).coeff a = 0 := by
  simp [erase]

