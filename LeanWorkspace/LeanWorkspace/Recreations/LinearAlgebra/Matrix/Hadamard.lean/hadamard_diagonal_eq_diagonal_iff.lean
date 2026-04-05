import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroClass α]

theorem hadamard_diagonal_eq_diagonal_iff {A : Matrix n n α} {d e} :
    A ⊙ diagonal d = diagonal e ↔ A.diag * d = e := by
  simp [Matrix.hadamard_diagonal, diagonal_eq_diagonal_iff, funext_iff]

