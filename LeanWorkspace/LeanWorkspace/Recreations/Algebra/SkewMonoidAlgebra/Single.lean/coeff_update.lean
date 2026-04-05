import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem coeff_update [DecidableEq α] : (f.update a b).coeff = Function.update f.coeff a b := by
  simp only [coeff, Function.update, Finsupp.update, Finsupp.coe_mk]
  congr!

