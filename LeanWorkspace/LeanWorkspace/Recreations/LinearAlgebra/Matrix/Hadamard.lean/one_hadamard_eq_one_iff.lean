import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem one_hadamard_eq_one_iff {A : Matrix n n α} : 1 ⊙ A = 1 ↔ A.diag = 1 := Matrix.one_hadamard_eq_diagonal_iff

