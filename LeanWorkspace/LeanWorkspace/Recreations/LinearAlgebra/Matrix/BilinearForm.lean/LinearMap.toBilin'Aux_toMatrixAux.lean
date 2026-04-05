import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

theorem LinearMap.toBilin'Aux_toMatrixAux [DecidableEq n] (B₂ : BilinForm R₁ (n → R₁)) :
    Matrix.toBilin'Aux (BilinForm.toMatrixAux (fun j => Pi.single j 1) B₂) = B₂ := by
  rw [BilinForm.toMatrixAux, Matrix.toBilin'Aux, toLinearMap₂'Aux_toMatrix₂Aux]

