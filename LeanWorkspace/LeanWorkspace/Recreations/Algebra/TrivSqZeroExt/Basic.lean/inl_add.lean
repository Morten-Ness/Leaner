import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) :
    (TrivSqZeroExt.inl (r₁ + r₂) : tsze R M) = TrivSqZeroExt.inl r₁ + TrivSqZeroExt.inl r₂ := TrivSqZeroExt.ext rfl (add_zero 0).symm

