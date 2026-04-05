import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem trace_mul_comm [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R) :
    Matrix.trace (A * B) = Matrix.trace (B * A) := by rw [← Matrix.trace_transpose, ← Matrix.trace_transpose_mul, transpose_mul]

