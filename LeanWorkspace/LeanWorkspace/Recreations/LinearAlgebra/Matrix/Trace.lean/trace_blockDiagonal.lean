import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_blockDiagonal [DecidableEq p] (M : p → Matrix n n R) :
    Matrix.trace (blockDiagonal M) = ∑ i, Matrix.trace (M i) := by
  simp [blockDiagonal, Matrix.trace, Finset.sum_comm (γ := n), Fintype.sum_prod_type]

