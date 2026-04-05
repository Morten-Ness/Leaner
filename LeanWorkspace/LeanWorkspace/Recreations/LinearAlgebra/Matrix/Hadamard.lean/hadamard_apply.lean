import Mathlib

variable {α m n R : Type*}

theorem hadamard_apply [Mul α] (A : Matrix m n α) (B : Matrix m n α) (i j) :
    Matrix.hadamard A B i j = A i j * B i j := rfl

