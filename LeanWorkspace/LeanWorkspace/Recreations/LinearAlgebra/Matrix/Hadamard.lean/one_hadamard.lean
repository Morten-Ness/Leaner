import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroOneClass α]

variable (M : Matrix n n α)

theorem one_hadamard : 1 ⊙ M = diagonal M.diag := one_mul M.diag ▸ Matrix.diagonal_hadamard M 1

