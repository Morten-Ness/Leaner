import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S] [AddCommGroup M] [AddCommGroup M₂]

variable {module_M : Module R M} {module_M₂ : Module S M₂} {σ : R →+* S}

variable (f : M →ₛₗ[σ] M₂)

theorem map_neg (x : M) : f (-x) = -f x := map_neg f x

