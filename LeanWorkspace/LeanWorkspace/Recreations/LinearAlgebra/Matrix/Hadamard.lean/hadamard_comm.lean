import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem hadamard_comm [CommMagma α] : A ⊙ B = B ⊙ A := ext fun _ _ => mul_comm _ _

-- associativity

