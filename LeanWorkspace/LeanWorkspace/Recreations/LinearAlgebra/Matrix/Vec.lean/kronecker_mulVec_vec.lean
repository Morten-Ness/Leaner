import Mathlib

open scoped Kronecker

variable [NonUnitalCommSemiring R] [Fintype m] [Fintype n]

theorem kronecker_mulVec_vec (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) :
    (B ⊗ₖ A) *ᵥ Matrix.vec X = Matrix.vec (A * X * Bᵀ) := Matrix.kronecker_mulVec_vec_of_commute _ _ _ fun _ _ _ => Commute.all _ _

