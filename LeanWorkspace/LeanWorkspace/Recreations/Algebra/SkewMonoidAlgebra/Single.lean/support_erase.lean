import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

theorem support_erase [DecidableEq α] : (f.erase a).support = f.support.erase a := by
  ext; simp [erase]

