import Mathlib

open scoped Kronecker

variable [Semiring R] [Fintype m] [Fintype n]

theorem vec_mul_eq_vecMul [DecidableEq m] (A : Matrix m n R) (B : Matrix n p R) :
    Matrix.vec (A * B) = A.vec ᵥ* (B ⊗ₖ 1) := by
  rw [Matrix.vec_vecMul_kronecker_of_commute, transpose_one, Matrix.one_mul]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

