import Mathlib

open scoped Kronecker

variable [NonUnitalSemiring R] [Fintype m] [Fintype n]

theorem kronecker_mulVec_vec_of_commute (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R)
    (hB : ∀ x i j, Commute x (B i j)) :
    (B ⊗ₖ A) *ᵥ Matrix.vec X = Matrix.vec (A * X * Bᵀ) := by
  ext ⟨k, l⟩
  simp_rw [Matrix.vec, mulVec, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hB ..).right_comm, Matrix.vec, (hB ..).eq]

