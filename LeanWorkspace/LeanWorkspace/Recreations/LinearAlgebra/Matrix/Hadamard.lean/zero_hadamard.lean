import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

variable [MulZeroClass α]

theorem zero_hadamard : (0 : Matrix m n α) ⊙ A = 0 := ext fun _ _ => zero_mul _

