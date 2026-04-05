import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

theorem single_add_erase (a : α) (f : SkewMonoidAlgebra M α) :
    single a (f.coeff a) + f.erase a = f := by
  apply toFinsupp_injective
  rw [single, ← toFinsupp_apply, toFinsupp_add, erase_apply_toFinsupp,
    Finsupp.single_add_erase]

