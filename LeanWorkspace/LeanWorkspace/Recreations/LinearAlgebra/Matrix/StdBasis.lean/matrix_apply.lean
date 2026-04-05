import Mathlib

variable {ι R M : Type*} (m n : Type*)

variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid M] [Module R M]

theorem matrix_apply (b : Module.Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n] :
    b.matrix m n (i, j, k) = Matrix.single i j (b k) := by
  simp [Module.Basis.matrix, Matrix.single_eq_of_single_single]

