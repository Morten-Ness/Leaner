import Mathlib

theorem vec_dotProduct_vec [AddCommMonoid R] [Mul R] [Fintype m] [Fintype n]
    (A B : Matrix m n R) :
    Matrix.vec A ⬝ᵥ Matrix.vec B = (Aᵀ * B).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

