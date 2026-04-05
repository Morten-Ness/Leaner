import Mathlib

open scoped Kronecker

variable [NonUnitalSemiring R] [Fintype m] [Fintype n]

theorem vec_vecMul_kronecker_of_commute (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R)
    (hA : ∀ x i j, Commute (A i j) x) :
    Matrix.vec X ᵥ* (B ⊗ₖ A) = Matrix.vec (Aᵀ * X * B) := by
  ext ⟨k, l⟩
  simp_rw [Matrix.vec, vecMul, mul_apply, dotProduct, kroneckerMap_apply, Finset.sum_mul, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product, (hA ..).eq, (hA ..).right_comm, mul_assoc, Matrix.vec]

