import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_sub [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R) :
    (TrivSqZeroExt.inl (r₁ - r₂) : tsze R M) = TrivSqZeroExt.inl r₁ - TrivSqZeroExt.inl r₂ := TrivSqZeroExt.ext rfl (sub_zero _).symm

