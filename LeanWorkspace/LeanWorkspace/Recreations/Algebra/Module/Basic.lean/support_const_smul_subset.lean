import Mathlib

variable {α R M M₂ : Type*}

theorem support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α → M) :
    support (a • f) ⊆ support f := Function.support_smul_subset_right (fun _ ↦ a) f

