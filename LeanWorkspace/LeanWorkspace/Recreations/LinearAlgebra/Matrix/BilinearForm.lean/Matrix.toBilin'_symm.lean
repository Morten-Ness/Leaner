import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem Matrix.toBilin'_symm :
    (Matrix.toBilin'.symm : _ ≃ₗ[R₁] Matrix n n R₁) = BilinForm.toMatrix' := BilinForm.toMatrix'.symm_symm

