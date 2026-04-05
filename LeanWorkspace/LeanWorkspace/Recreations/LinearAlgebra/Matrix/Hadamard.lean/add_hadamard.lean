import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem add_hadamard [Distrib α] : (B + C) ⊙ A = B ⊙ A + C ⊙ A := ext fun _ _ => right_distrib _ _ _

-- scalar multiplication

