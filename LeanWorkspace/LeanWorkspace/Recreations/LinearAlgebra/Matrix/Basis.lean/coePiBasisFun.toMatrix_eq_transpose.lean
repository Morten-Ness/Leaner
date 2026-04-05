import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem coePiBasisFun.toMatrix_eq_transpose [Finite ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R → Matrix ι ι R) = Matrix.transpose := by
  ext M i j
  rfl

