import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem det_eq_sum_mul_adjugate_col (A : Matrix n n α) (j : n) :
    det A = ∑ i : n, A i j * Matrix.adjugate A j i := by
  simpa only [det_transpose, ← Matrix.adjugate_transpose] using Matrix.det_eq_sum_mul_adjugate_row Aᵀ j

