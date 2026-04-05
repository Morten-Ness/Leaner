import Mathlib

variable {α m n R : Type*}

variable (A : Matrix m n α) (B : Matrix m n α) (C : Matrix m n α)

theorem conjTranspose_hadamard [Mul α] [StarMul α] (A B : Matrix m n α) : (A ⊙ B)ᴴ = Bᴴ ⊙ Aᴴ := ext fun _ _ => StarMul.star_mul _ _

