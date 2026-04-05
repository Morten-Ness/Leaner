import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_multiset_sum (s : Multiset (Matrix n n R)) : Matrix.trace s.sum = (s.map Matrix.trace).sum := map_multiset_sum (Matrix.traceAddMonoidHom n R) s

