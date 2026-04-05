import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂]

theorem map_zero {f : M → M₂} (lin : IsLinearMap R f) : f (0 : M) = (0 : M₂) := LinearMap.map_zero (lin.mk' f)

