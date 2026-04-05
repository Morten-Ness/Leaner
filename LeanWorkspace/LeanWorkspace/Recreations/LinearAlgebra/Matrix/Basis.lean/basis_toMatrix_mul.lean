import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)

variable (f : M →ₗ[R] N)

variable [Fintype ι']

theorem basis_toMatrix_mul [Fintype κ] [Finite ι] [DecidableEq κ]
    (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N) (A : Matrix ι' κ R) :
    b₁.toMatrix b₂ * A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) := by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this

