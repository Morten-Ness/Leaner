import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {N N₂ : Type*}

variable [CommSemiring R] [CommSemiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]

variable [AddCommMonoid N] [AddCommMonoid N₂] [Module R N] [Module R N₂]

variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}

variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]

variable (p : Submodule R M) (q : Submodule R₂ M₂)

variable (pₗ : Submodule R N) (qₗ : Submodule R N₂)

theorem comap_le_comap_smul (fₗ : N →ₗ[R] N₂) (c : R) : Submodule.comap fₗ qₗ ≤ Submodule.comap (c • fₗ) qₗ := by
  simp only [SetLike.le_def, Submodule.mem_comap, LinearMap.smul_apply]
  exact fun _ h ↦ smul_mem _ _ h

