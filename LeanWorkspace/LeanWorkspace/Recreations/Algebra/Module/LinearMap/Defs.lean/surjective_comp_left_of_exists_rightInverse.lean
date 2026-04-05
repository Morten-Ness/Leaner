import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}

variable {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂)

variable {f g} {f' : M₂ →ₛₗ[σ₂₃] M₃} {g' : M₁ →ₛₗ[σ₁₂] M₂}

theorem surjective_comp_left_of_exists_rightInverse {σ₃₂ : R₃ →+* R₂}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂]
    (hf : ∃ f' : M₃ →ₛₗ[σ₃₂] M₂, f.comp f' = .id) :
    Function.Surjective fun g : M₁ →ₛₗ[σ₁₂] M₂ ↦ f.comp g := by
  intro h
  obtain ⟨f', hf'⟩ := hf
  refine ⟨f'.comp h, ?_⟩
  simp_rw [← LinearMap.comp_assoc, hf', LinearMap.id_comp]

