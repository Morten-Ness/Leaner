import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable {x : M}

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

variable [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂}

variable (hf : Function.Surjective f)

theorem lt_map_of_comap_lt_of_surjective (h : q.comap f < p) : q < p.map f := by
  rw [lt_iff_le_not_ge] at h ⊢; rw [Submodule.map_le_iff_le_comap]
  exact h.imp_left (Submodule.le_map_of_comap_le_of_surjective hf)

