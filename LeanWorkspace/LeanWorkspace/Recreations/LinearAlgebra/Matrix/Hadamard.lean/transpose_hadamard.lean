import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem transpose_hadamard [Mul α] (A B : Matrix m n α) : (A ⊙ B)ᵀ = Aᵀ ⊙ Bᵀ := ext fun _ _ => rfl

