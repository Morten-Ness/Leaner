import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [DecidableEq n] [MulZeroClass α]

theorem hadamard_diagonal (M) (w : n → α) :
    M ⊙ diagonal w = diagonal (M.diag * w) := by aesop (add simp diagonal)

