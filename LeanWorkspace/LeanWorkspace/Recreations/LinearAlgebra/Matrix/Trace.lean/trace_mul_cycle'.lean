import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem trace_mul_cycle' [NonUnitalCommSemiring R] (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) : Matrix.trace (A * (B * C)) = Matrix.trace (C * (A * B)) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]

