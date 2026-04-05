import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {M : Type*} {M₂ : Type*}

variable [Ring R] [Ring R₂]

variable [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

theorem eqLocus_eq_ker_sub (f g : M →ₛₗ[τ₁₂] M₂) : LinearMap.eqLocus f g = ker (f - g) := SetLike.ext fun _ => sub_eq_zero.symm

