import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroClass α]

theorem diagonal_hadamard (M) (w : n → α) :
    diagonal w ⊙ M = diagonal (w * M.diag) := by aesop (add simp diagonal)

