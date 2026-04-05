import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {ι : Type*}

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

variable {f' : M →ₗ[R] M}

theorem _root_.Module.End.pow_restrict {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p)
    (h' := Module.End.pow_apply_mem_of_forall_mem n h) :
    (f'.restrict h) ^ n = (f' ^ n).restrict h' := by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ ↦ LinearMap.restrict_coe_apply _ _ _
  simp [Module.End.coe_pow, this.iterate_right _ _]

