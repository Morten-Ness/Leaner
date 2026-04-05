import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroClass α]

theorem diagonal_hadamard_eq_diagonal_iff {A : Matrix n n α} {d e} :
    diagonal d ⊙ A = diagonal e ↔ d * A.diag = e := by
  simp [Matrix.diagonal_hadamard, diagonal_eq_diagonal_iff, funext_iff]

