import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_comp_inl [Zero M] : TrivSqZeroExt.snd ∘ (TrivSqZeroExt.inl : R → tsze R M) = 0 := rfl

