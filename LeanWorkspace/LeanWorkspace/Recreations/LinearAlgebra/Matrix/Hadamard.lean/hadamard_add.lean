import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem hadamard_add [Distrib α] : A ⊙ (B + C) = A ⊙ B + A ⊙ C := ext fun _ _ => left_distrib _ _ _

