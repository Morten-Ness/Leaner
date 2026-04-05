import Mathlib

open scoped Kronecker

variable [Semiring R] [Fintype m] [Fintype n]

theorem vec_mul_eq_mulVec [DecidableEq n] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix.vec (A * B) = (1 ⊗ₖ A) *ᵥ Matrix.vec B := by
  rw [Matrix.kronecker_mulVec_vec_of_commute, transpose_one, Matrix.mul_one]
  intro x i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

