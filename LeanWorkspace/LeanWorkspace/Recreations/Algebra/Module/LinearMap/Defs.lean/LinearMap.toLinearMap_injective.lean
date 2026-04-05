import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable {σ : R →+* S}

theorem toLinearMap_injective {F : Type*} [FunLike F M M₃] [SemilinearMapClass F σ M M₃]
    {f g : F} (h : (f : M →ₛₗ[σ] M₃) = (g : M →ₛₗ[σ] M₃)) :
    f = g := by
  apply DFunLike.ext
  intro m
  exact DFunLike.congr_fun h m

