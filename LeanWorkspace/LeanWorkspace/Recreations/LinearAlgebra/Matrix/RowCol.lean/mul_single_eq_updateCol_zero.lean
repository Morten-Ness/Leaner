import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem mul_single_eq_updateCol_zero
    [DecidableEq m] [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : m) (j : n) (r : α) :
    A * single i j r = Matrix.updateCol 0 j (A.col i <• r) := by
  rw [Matrix.single_eq_updateCol_zero, Matrix.mul_updateCol, Matrix.mul_zero, mulVec_single]

