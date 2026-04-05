import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂]

theorem mk'_apply {f : M → M₂} (lin : IsLinearMap R f) (x : M) : IsLinearMap.mk' f lin x = f x := rfl

