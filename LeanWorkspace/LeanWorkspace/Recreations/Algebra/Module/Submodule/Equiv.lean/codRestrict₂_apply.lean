import Mathlib

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {N : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₁] [Module R M₂] [Module R M₃]

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M) (i : M₃ →ₗ[R] M) (hi : Function.Injective i)
  (hf : ∀ x y, f x y ∈ LinearMap.range i)

theorem codRestrict₂_apply (x : M₁) (y : M₂) :
    i (LinearMap.codRestrict₂ f i hi hf x y) = f x y := by
  simp [LinearMap.codRestrict₂]

