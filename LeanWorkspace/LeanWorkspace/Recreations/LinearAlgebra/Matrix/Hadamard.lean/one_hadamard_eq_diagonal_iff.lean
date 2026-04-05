import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem one_hadamard_eq_diagonal_iff {A : Matrix n n α} {d} : 1 ⊙ A = diagonal d ↔ A.diag = d := by
  simpa using Matrix.diagonal_hadamard_eq_diagonal_iff (A := A) (d := 1)

