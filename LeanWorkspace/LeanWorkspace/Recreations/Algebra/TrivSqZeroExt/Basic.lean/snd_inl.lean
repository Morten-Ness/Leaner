import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_inl [Zero M] (r : R) : (TrivSqZeroExt.inl r : tsze R M).snd = 0 := rfl

