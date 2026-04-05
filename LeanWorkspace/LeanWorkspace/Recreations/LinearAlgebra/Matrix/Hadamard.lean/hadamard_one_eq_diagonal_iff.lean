import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem hadamard_one_eq_diagonal_iff {A : Matrix n n α} {d} : A ⊙ 1 = diagonal d ↔ A.diag = d := by
  simpa using Matrix.hadamard_diagonal_eq_diagonal_iff (A := A) (d := 1)

