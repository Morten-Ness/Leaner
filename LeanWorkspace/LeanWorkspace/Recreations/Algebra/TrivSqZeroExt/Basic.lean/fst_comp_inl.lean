import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_comp_inl [Zero M] : TrivSqZeroExt.fst ∘ (TrivSqZeroExt.inl : R → tsze R M) = id := rfl

