import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem BilinForm.toMatrix'_toBilin' (M : Matrix n n R₁) :
    BilinForm.toMatrix' (Matrix.toBilin' M) = M := (LinearMap.toMatrix₂' R₁).apply_symm_apply M

