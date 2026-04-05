import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem Matrix.toBilin'_toMatrix' (B : BilinForm R₁ (n → R₁)) :
    Matrix.toBilin' (BilinForm.toMatrix' B) = B := Matrix.toBilin'.apply_symm_apply B

