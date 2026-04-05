import Mathlib

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

variable [CommSemiring R]

theorem mul_kroneckerTMul_mul
    [NonUnitalSemiring α] [NonUnitalSemiring β] [Module R α] [Module R β]
    [IsScalarTower R α α] [SMulCommClass R α α] [IsScalarTower R β β] [SMulCommClass R β β]
    [Fintype m] [Fintype m'] (A : Matrix l m α) (B : Matrix m n α)
    (A' : Matrix l' m' β) (B' : Matrix m' n' β) :
    (A * B) ⊗ₖₜ[R] (A' * B') = A ⊗ₖₜ[R] A' * B ⊗ₖₜ[R] B' := Matrix.kroneckerMapBilinear_mul_mul (TensorProduct.mk R α β) tmul_mul_tmul A B A' B'

