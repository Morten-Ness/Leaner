import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [MulZeroClass α]

theorem hadamard_zero : A ⊙ (0 : Matrix m n α) = 0 := ext fun _ _ => mul_zero _

