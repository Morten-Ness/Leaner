import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_blockDiagonal' [DecidableEq p] {m : p → Type*} [∀ i, Fintype (m i)]
    (M : ∀ i, Matrix (m i) (m i) R) :
    Matrix.trace (blockDiagonal' M) = ∑ i, Matrix.trace (M i) := by
  simp [blockDiagonal', Matrix.trace, Finset.sum_sigma']

