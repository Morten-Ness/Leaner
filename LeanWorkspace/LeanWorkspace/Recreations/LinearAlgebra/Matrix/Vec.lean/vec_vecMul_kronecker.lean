import Mathlib

open scoped Kronecker

variable [NonUnitalCommSemiring R] [Fintype m] [Fintype n]

theorem vec_vecMul_kronecker (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) :
    Matrix.vec X ᵥ* (B ⊗ₖ A) = Matrix.vec (Aᵀ * X * B) := Matrix.vec_vecMul_kronecker_of_commute _ _ _ fun _ _ _ => Commute.all _ _

