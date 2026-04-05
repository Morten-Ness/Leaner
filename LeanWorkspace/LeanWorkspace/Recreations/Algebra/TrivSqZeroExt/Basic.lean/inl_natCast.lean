import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem inl_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (TrivSqZeroExt.inl n : tsze R M) = n := rfl

