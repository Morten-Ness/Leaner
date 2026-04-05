import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommGroup R]

theorem trace_neg (A : Matrix n n R) : Matrix.trace (-A) = -Matrix.trace A := Finset.sum_neg_distrib ..

