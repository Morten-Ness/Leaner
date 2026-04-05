import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inr_add [AddZeroClass R] [Add M] (m₁ m₂ : M) :
    (TrivSqZeroExt.inr (m₁ + m₂) : tsze R M) = TrivSqZeroExt.inr m₁ + TrivSqZeroExt.inr m₂ := TrivSqZeroExt.ext (add_zero 0).symm rfl

