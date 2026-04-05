import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {ι : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

theorem _root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M}
    {g : Module.End R N} {G : Module.End R M} (h : G.comp N.subtype = N.subtype.comp g) {k : ℕ}
    (hG : G ^ k = 0) : g ^ k = 0 := by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← Module.End.commute_pow_left_of_commute h, hG, zero_comp, zero_apply]
  simpa using hg

