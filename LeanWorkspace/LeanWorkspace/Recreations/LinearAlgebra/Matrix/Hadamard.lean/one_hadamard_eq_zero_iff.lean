import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem one_hadamard_eq_zero_iff {A : Matrix n n α} : 1 ⊙ A = 0 ↔ A.diag = 0 := by
  simpa using Matrix.one_hadamard_eq_diagonal_iff (A := A) (d := 0)

