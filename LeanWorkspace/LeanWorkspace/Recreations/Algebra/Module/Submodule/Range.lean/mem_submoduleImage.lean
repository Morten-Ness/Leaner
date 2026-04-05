import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

theorem mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yO : y ∈ O), y ∈ N ∧ ϕ ⟨y, yO⟩ = x := by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩

