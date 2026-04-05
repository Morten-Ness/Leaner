import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {M : Type*} {M₂ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

include τ₁₂ in
theorem eqOn_sup {f g : F} {S T : Submodule R M} (hS : Set.EqOn f g S) (hT : Set.EqOn f g T) :
    Set.EqOn f g ↑(S ⊔ T) := by
  rw [← LinearMap.le_eqLocus] at hS hT ⊢
  exact sup_le hS hT

