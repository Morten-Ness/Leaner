import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Ring R] [Ring R₂]

variable [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

variable {f : M →ₛₗ[τ₁₂] M₂}

theorem sub_mem_ker_iff {x y} : x - y ∈ LinearMap.ker f ↔ f x = f y := by rw [LinearMap.mem_ker, map_sub, sub_eq_zero]

