import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Semiring R] [Module R M] [Semiring S] [Module S M₂] [Module R M₃]

variable {σ : R →+* S}

theorem toLinearMap_injective {f g : M →ₑ+[σ.toMonoidHom] M₂}
    (h : (f : M →ₛₗ[σ] M₂) = (g : M →ₛₗ[σ] M₂)) :
    f = g := by
  ext m
  exact LinearMap.congr_fun h m

