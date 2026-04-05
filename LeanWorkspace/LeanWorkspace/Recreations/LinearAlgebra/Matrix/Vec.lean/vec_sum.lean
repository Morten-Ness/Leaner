import Mathlib

theorem vec_sum [AddCommMonoid R] (s : Finset ι) (A : ι → Matrix m n R) :
    Matrix.vec (∑ i ∈ s, A i) = ∑ i ∈ s, Matrix.vec (A i) := by
  ext
  simp_rw [Matrix.vec, Finset.sum_apply, Matrix.vec, Matrix.sum_apply]

