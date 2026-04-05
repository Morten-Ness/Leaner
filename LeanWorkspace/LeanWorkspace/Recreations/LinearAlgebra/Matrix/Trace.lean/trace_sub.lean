import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommGroup R]

theorem trace_sub (A B : Matrix n n R) : Matrix.trace (A - B) = Matrix.trace A - Matrix.trace B := Finset.sum_sub_distrib ..

