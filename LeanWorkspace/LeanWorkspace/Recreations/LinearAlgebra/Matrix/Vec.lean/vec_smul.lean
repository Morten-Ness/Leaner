import Mathlib

theorem vec_smul {α} [SMul α R] (r : α) (A : Matrix m n R) : Matrix.vec (r • A) = r • Matrix.vec A := rfl

