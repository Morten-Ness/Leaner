import Mathlib

theorem vec_neg [Neg R] (A : Matrix m n R) : Matrix.vec (-A) = -Matrix.vec A := rfl

