import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {M : Type*} {M₂ : Type*}

variable [Semiring R] [Semiring R₂]

variable [AddCommMonoid M] [AddCommMonoid M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

theorem le_eqLocus {f g : F} {S : Submodule R M} : S ≤ LinearMap.eqLocus f g ↔ Set.EqOn f g S := Iff.rfl

