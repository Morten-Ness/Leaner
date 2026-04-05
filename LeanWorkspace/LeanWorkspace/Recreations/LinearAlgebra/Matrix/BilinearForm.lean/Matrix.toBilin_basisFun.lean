import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

theorem Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBilin' := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]

