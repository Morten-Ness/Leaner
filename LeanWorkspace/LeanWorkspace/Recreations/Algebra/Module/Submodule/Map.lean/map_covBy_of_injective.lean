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

variable (hf : Function.Injective f)

theorem map_covBy_of_injective {p q : Submodule R M} (h : p ⋖ q) :
    p.map f ⋖ q.map f := by
  refine ⟨lt_of_le_of_ne (Submodule.map_mono h.1.le) ((Submodule.map_injective_of_injective hf).ne h.1.ne), ?_⟩
  intro P h₁ h₂
  refine h.2 ?_ (Submodule.comap_lt_of_lt_map_of_injective hf h₂)
  rw [← Submodule.map_lt_map_iff_of_injective hf]
  refine h₁.trans_le ?_
  exact (Set.image_preimage_eq_of_subset (.trans h₂.le (Set.image_subset_range _ _))).superset

