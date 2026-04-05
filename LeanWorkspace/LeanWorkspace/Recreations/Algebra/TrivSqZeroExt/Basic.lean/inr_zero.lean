import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inr_zero [Zero R] [Zero M] : (TrivSqZeroExt.inr 0 : tsze R M) = 0 := rfl

