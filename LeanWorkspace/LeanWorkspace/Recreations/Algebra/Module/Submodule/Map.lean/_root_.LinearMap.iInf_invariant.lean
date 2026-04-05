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

theorem _root_.LinearMap.iInf_invariant {σ : R →+* R} {ι : Sort*}
    (f : M →ₛₗ[σ] M) {p : ι → Submodule R M} (hf : ∀ i, ∀ v ∈ p i, f v ∈ p i) :
    ∀ v ∈ iInf p, f v ∈ iInf p := by
  simp only [mem_iInf]
  exact fun v a i ↦ hf i v (a i)

