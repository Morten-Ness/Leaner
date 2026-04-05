import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

theorem coeff_erase_ne (h : a' ≠ a) : (f.erase a).coeff a' = f.coeff a' := by
  simp [erase, h]

