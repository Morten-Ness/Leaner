import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R M₂]

theorem map_neg {f : M → M₂} (lin : IsLinearMap R f) (x : M) : f (-x) = -f x := LinearMap.map_neg (lin.mk' f) x

