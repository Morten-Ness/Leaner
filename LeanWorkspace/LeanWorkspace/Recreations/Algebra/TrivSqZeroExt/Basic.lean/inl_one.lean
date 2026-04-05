import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_one [One R] [Zero M] : (TrivSqZeroExt.inl 1 : tsze R M) = 1 := rfl

