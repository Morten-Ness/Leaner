import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_list_sum (l : List (Matrix n n R)) : Matrix.trace l.sum = (l.map Matrix.trace).sum := map_list_sum (Matrix.traceAddMonoidHom n R) l

