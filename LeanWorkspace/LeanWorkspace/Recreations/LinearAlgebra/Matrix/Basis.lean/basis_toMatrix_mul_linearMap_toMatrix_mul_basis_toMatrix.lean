import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

variable [Fintype ι']

variable [Finite κ] [Fintype ι]

theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    [Fintype κ'] [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c f := by
  cases nonempty_fintype κ
  rw [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]

