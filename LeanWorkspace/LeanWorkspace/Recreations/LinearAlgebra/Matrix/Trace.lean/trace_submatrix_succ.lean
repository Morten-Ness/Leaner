import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem trace_submatrix_succ {n : ℕ} [AddCommMonoid R]
    (M : Matrix (Fin n.succ) (Fin n.succ) R) :
    M 0 0 + Matrix.trace (submatrix M Fin.succ Fin.succ) = Matrix.trace M := by
  delta Matrix.trace
  rw [← (finSuccEquiv n).symm.sum_comp]
  simp

