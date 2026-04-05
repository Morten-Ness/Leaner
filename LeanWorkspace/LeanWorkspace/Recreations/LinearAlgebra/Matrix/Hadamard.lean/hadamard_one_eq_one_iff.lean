import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem hadamard_one_eq_one_iff {A : Matrix n n α} : A ⊙ 1 = 1 ↔ A.diag = 1 := Matrix.hadamard_one_eq_diagonal_iff

