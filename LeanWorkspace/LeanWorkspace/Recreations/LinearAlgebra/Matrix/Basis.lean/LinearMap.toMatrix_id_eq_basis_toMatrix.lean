import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

theorem LinearMap.toMatrix_id_eq_basis_toMatrix [Fintype ι] [DecidableEq ι] [Finite ι'] :
    LinearMap.toMatrix b b' id = b'.toMatrix b := by
  ext i
  apply LinearMap.toMatrix_apply

