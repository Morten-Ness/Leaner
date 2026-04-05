import Mathlib

theorem star_vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Star R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    star (Matrix.vec A) ⬝ᵥ Matrix.vec B = (Aᴴ * B).trace := by
  simp_rw [Matrix.star_vec, Matrix.vec_dotProduct_vec, ← conjTranspose_transpose, transpose_transpose]

