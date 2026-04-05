import Mathlib

variable {k G H : Type*}

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

theorem coeff_erase_apply [DecidableEq α] :
    (f.erase a).coeff a' = if a' = a then 0 else f.coeff a' := ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl)

