import Mathlib

theorem vec_add [Add R] (A B : Matrix m n R) : Matrix.vec (A + B) = Matrix.vec A + Matrix.vec B := rfl

