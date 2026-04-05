import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (TrivSqZeroExt.inl z : tsze R M) = z := rfl

