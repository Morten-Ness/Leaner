import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_zero [Zero R] [Zero M] : (TrivSqZeroExt.inl 0 : tsze R M) = 0 := rfl

