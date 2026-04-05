import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

theorem toMatrix_mul_toMatrix {ι'' : Type*} [Fintype ι'] (b'' : ι'' → M) :
    b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b'' := by
  haveI := Classical.decEq ι
  haveI := Classical.decEq ι'
  haveI := Classical.decEq ι''
  ext i j
  simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, sum_repr_mul_repr]

