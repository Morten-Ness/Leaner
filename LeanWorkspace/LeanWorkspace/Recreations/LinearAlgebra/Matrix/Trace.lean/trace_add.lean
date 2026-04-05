import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_add (A B : Matrix n n R) : Matrix.trace (A + B) = Matrix.trace A + Matrix.trace B := Finset.sum_add_distrib

