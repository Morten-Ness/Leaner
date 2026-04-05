import Mathlib

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']

variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]

variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']

variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]

variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']

variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

theorem IsLocalizedModule.map_exact (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) (ex : Function.Exact g h) :
    Function.Exact (map S f₀ f₁ g) (map S f₁ f₂ h) := Function.Exact.of_ladder_linearEquiv_of_exact
    (map_iso_commute S f₀ f₁ g) (map_iso_commute S f₁ f₂ h) (LocalizedModule.map_exact S g h ex)

