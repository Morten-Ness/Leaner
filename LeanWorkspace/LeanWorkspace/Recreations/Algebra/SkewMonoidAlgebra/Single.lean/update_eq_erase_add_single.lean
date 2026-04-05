import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

theorem update_eq_erase_add_single : f.update a b = f.erase a + single a b := by
  classical ext x; by_cases hx : x = a <;> aesop (add norm coeff_single_apply)

