import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem hadamard_one : M ⊙ 1 = diagonal M.diag := mul_one M.diag ▸ Matrix.hadamard_diagonal M 1

