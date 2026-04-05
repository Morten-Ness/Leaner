import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {N : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₁] [Module R M₂] [Module R M₃]

variable (f : M₁ →ₗ[R] M₂) (i : M₃ →ₗ[R] M₂) (hi : Function.Injective i)
  (hf : ∀ x, f x ∈ LinearMap.range i)

theorem codRestrictOfInjective_comp :
    i ∘ₗ LinearMap.codRestrictOfInjective f i hi hf = f := by
  ext
  simp

